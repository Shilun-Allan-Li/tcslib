#!/usr/bin/env python3
"""D7 split analyzer: block parse, private-family clustering, legal cut points.

A cut between top-level blocks is legal iff no private family spans it:
every reference to a private must stay in the private's own file.
Clusters are the union-find closure of "block references private p" edges.
"""
import re
import sys
from pathlib import Path

DECL_RE = re.compile(
    r"^(private\s+)?(?:noncomputable\s+)?(?:@\[[^\]]*\]\s*)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([A-Za-z0-9_.']+)"
)
START_KEYWORDS = (
    "private ", "noncomputable ", "@[", "theorem ", "lemma ", "def ",
    "abbrev ", "structure ", "inductive ", "instance ", "open ",
    "section", "end ", "end", "variable ", "variable(", "attribute ",
    "set_option ", "namespace ", "/--", "/-!", "/-", "--",
)


def parse_blocks(lines, body_start, body_end):
    """Return list of (start, end, kind, name_or_None, private?) line-index blocks.
    Comment blocks are merged into the following block."""
    starts = []
    depth = 0  # block-comment nesting
    for i in range(body_start, body_end):
        ln = lines[i]
        if depth == 0:
            stripped = ln
            if stripped and not stripped[0].isspace():
                if any(stripped.startswith(k) for k in START_KEYWORDS):
                    starts.append(i)
        # update comment depth (approximate: count /- and -/ occurrences)
        depth += ln.count("/-") - ln.count("-/")
        if depth < 0:
            depth = 0
    starts.append(body_end)
    raw = [(starts[j], starts[j + 1]) for j in range(len(starts) - 1)]
    # merge comment-only blocks into the next block
    blocks = []
    pending = None
    for (a, b) in raw:
        first = lines[a]
        is_comment = first.startswith(("/--", "/-!", "/-", "--"))
        if is_comment:
            if pending is None:
                pending = a
            continue
        start = pending if pending is not None else a
        pending = None
        m = DECL_RE.match(first)
        if m:
            blocks.append([start, b, "decl", m.group(3), bool(m.group(1))])
        else:
            kind = first.split()[0] if first.split() else "blank"
            blocks.append([start, b, kind, None, False])
    if pending is not None:
        blocks.append([pending, body_end, "trailing-comment", None, False])
    return blocks


def analyze(path, body_start, body_end, atomic_ranges=()):
    lines = Path(path).read_text(encoding="utf-8").split("\n")
    blocks = parse_blocks(lines, body_start, body_end)
    # fold atomic ranges (e.g. section..end section) into single pseudo-blocks
    for (lo, hi) in atomic_ranges:
        merged, acc, span = [], None, None
        for b in blocks:
            if lo <= b[0] < hi:
                if acc is None:
                    acc = [b[0], b[1], "atomic", f"section@{lo}", False]
                else:
                    acc[1] = b[1]
            else:
                if acc is not None:
                    merged.append(acc)
                    acc = None
                merged.append(b)
        if acc is not None:
            merged.append(acc)
        blocks = merged

    def strip_comments(text):
        # remove nested block comments and -- line comments (code refs only)
        out, i, depth, n = [], 0, 0, len(text)
        while i < n:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i) and depth > 0:
                depth -= 1
                i += 2
            elif depth == 0 and text.startswith("--", i):
                j = text.find("\n", i)
                i = n if j == -1 else j
            else:
                if depth == 0:
                    out.append(text[i])
                i += 1
        return "".join(out)

    texts = [strip_comments("\n".join(lines[b[0]:b[1]])) for b in blocks]
    privates = {}
    for idx, b in enumerate(blocks):
        if b[4]:
            privates[b[3]] = idx
        if b[2] == "atomic":  # privates inside atomic sections
            for m in re.finditer(r"^private\s+(?:noncomputable\s+)?"
                                 r"(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s+"
                                 r"([A-Za-z0-9_.']+)", texts[idx], re.M):
                privates[m.group(1)] = idx

    parent = list(range(len(blocks)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    pat = {name: re.compile(r"(?<![A-Za-z0-9_.'])" + re.escape(name) + r"(?![A-Za-z0-9_'])")
           for name in privates}
    for idx, text in enumerate(texts):
        for name, didx in privates.items():
            if idx == didx:
                continue
            if pat[name].search(text):
                union(idx, didx)

    spans = {}
    for idx in range(len(blocks)):
        r = find(idx)
        lo, hi = spans.get(r, (idx, idx))
        spans[r] = (min(lo, idx), max(hi, idx))

    illegal = set()
    for (lo, hi) in spans.values():
        for cut in range(lo, hi):
            illegal.add(cut)
    legal = [i for i in range(len(blocks) - 1) if i not in illegal]

    nlines = body_end - body_start
    print(f"\n### {path}")
    print(f"body lines {body_start+1}-{body_end}: {nlines} lines, "
          f"{len(blocks)} blocks, {len(privates)} privates, "
          f"{sum(1 for s in spans.values() if s[0] != s[1])} multi-block clusters")
    big = sorted(((hi - lo, lo, hi) for (lo, hi) in spans.values()), reverse=True)[:5]
    for (sz, lo, hi) in big:
        if sz:
            print(f"  cluster span blocks {lo}-{hi}: lines {blocks[lo][0]+1}-{blocks[hi][1]} "
                  f"({blocks[hi][1]-blocks[lo][0]} lines)")
    # greedy pack: largest legal parts <= target
    target = 1100
    print(f"  legal cuts: {len(legal)}")
    parts, prev = [], body_start
    last_ok = None
    li = 0
    for cutpos in range(len(blocks) - 1):
        endline = blocks[cutpos][1]
        if cutpos in set(legal):
            if endline - prev <= target:
                last_ok = (cutpos, endline)
            else:
                if last_ok is None:
                    # forced oversize part: extend to this legal cut
                    parts.append((prev, endline))
                    prev = endline
                else:
                    parts.append((prev, last_ok[1]))
                    prev = last_ok[1]
                    last_ok = (cutpos, endline) if endline - prev <= target else None
    parts.append((prev, body_end))
    print(f"  greedy parts (target {target}): " +
          ", ".join(f"{b - a}" for (a, b) in parts))
    return blocks, legal, spans


FILES = [
    ("TCSlib/Complexity/TuringMachine/Build/Loop.lean", 116, 2698, ()),
    ("TCSlib/Complexity/TuringMachine/Build/Primitives.lean", 121, 4418, ()),
    ("TCSlib/Complexity/ClassNP/EXP.lean", 53, 2887, ((411, 582),)),
    ("TCSlib/Complexity/ClassNP/Nondeterminism.lean", 65, 2627, ()),
    ("TCSlib/Complexity/ClassNP/TMSAT.lean", 92, 1908, ()),
]

if __name__ == "__main__":
    for (p, a, b, atomic) in FILES:
        analyze(p, a, b, atomic)


def cut_costs(path, body_start, body_end, atomic_ranges=()):
    lines = Path(path).read_text(encoding="utf-8").split("\n")
    blocks = parse_blocks(lines, body_start, body_end)
    for (lo, hi) in atomic_ranges:
        merged, acc = [], None
        for b in blocks:
            if lo <= b[0] < hi:
                if acc is None:
                    acc = [b[0], b[1], "atomic", f"section@{lo}", False]
                else:
                    acc[1] = b[1]
            else:
                if acc is not None:
                    merged.append(acc); acc = None
                merged.append(b)
        if acc is not None:
            merged.append(acc)
        blocks = merged

    def strip_comments(text):
        out, i, depth, n = [], 0, 0, len(text)
        while i < n:
            if text.startswith("/-", i):
                depth += 1; i += 2
            elif text.startswith("-/", i) and depth > 0:
                depth -= 1; i += 2
            elif depth == 0 and text.startswith("--", i):
                j = text.find("\n", i); i = n if j == -1 else j
            else:
                if depth == 0:
                    out.append(text[i])
                i += 1
        return "".join(out)

    texts = [strip_comments("\n".join(lines[b[0]:b[1]])) for b in blocks]
    privates = {}
    for idx, b in enumerate(blocks):
        if b[4]:
            privates[b[3]] = idx
        if b[2] == "atomic":
            for m in re.finditer(r"private\s+(?:noncomputable\s+)?"
                                 r"(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s+"
                                 r"([A-Za-z0-9_.']+)", texts[idx]):
                privates[m.group(1)] = idx
    lastref = {}
    pats = {n: re.compile(r"(?<![A-Za-z0-9_.'])" + re.escape(n) + r"(?![A-Za-z0-9_'])")
            for n in privates}
    for name, didx in privates.items():
        last = didx
        for idx in range(didx + 1, len(blocks)):
            if pats[name].search(texts[idx]):
                last = idx
        lastref[name] = last

    nb = len(blocks)
    print(f"\n### cut costs: {path}")
    results = []
    for i in range(nb - 1):
        spanning = [n for n, d in privates.items() if d <= i < lastref[n]]
        endline = blocks[i][1]
        results.append((i, endline, len(spanning), spanning))
    # print local minima at reasonable positions
    best = sorted(results, key=lambda r: (r[2], abs(r[1] - (body_start + (body_end-body_start)//2))))
    seen = 0
    for (i, endline, c, names) in sorted(best[:14], key=lambda r: r[1]):
        part1 = endline - body_start
        part2 = body_end - endline
        print(f"  cut after line {endline}: cost {c:3d}  parts {part1}/{part2}"
              + (f"  hubs: {', '.join(names[:8])}" + ("..." if len(names) > 8 else "") if c and c <= 12 else ""))
        seen += 1


for (p, a, b, atomic) in FILES:
    cut_costs(p, a, b, atomic)


def min_promotions(path, body_start, body_end, atomic_ranges=(), limit=1100):
    lines = Path(path).read_text(encoding="utf-8").split("\n")
    blocks = parse_blocks(lines, body_start, body_end)
    for (lo, hi) in atomic_ranges:
        merged, acc = [], None
        for b in blocks:
            if lo <= b[0] < hi:
                if acc is None:
                    acc = [b[0], b[1], "atomic", f"section@{lo}", False]
                else:
                    acc[1] = b[1]
            else:
                if acc is not None:
                    merged.append(acc); acc = None
                merged.append(b)
        if acc is not None:
            merged.append(acc)
        blocks = merged

    def strip_comments(text):
        out, i, depth, n = [], 0, 0, len(text)
        while i < n:
            if text.startswith("/-", i):
                depth += 1; i += 2
            elif text.startswith("-/", i) and depth > 0:
                depth -= 1; i += 2
            elif depth == 0 and text.startswith("--", i):
                j = text.find("\n", i); i = n if j == -1 else j
            else:
                if depth == 0:
                    out.append(text[i])
                i += 1
        return "".join(out)

    texts = [strip_comments("\n".join(lines[b[0]:b[1]])) for b in blocks]
    privates = {}
    for idx, b in enumerate(blocks):
        if b[4]:
            privates[b[3]] = idx
        if b[2] == "atomic":
            for m in re.finditer(r"private\s+(?:noncomputable\s+)?"
                                 r"(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s+"
                                 r"([A-Za-z0-9_.']+)", texts[idx]):
                privates[m.group(1)] = idx
    pats = {n: re.compile(r"(?<![A-Za-z0-9_.'])" + re.escape(n) + r"(?![A-Za-z0-9_'])")
            for n in privates}
    span = {}
    for name, didx in privates.items():
        last = didx
        for idx in range(didx + 1, len(blocks)):
            if pats[name].search(texts[idx]):
                last = idx
        span[name] = (didx, last)

    nb = len(blocks)
    # contained(i, j): privates with def > i and lastref <= j  (0-indexed blocks i+1..j)
    # f(j) = max contained over partitions of blocks[0..j] with each part <= limit lines
    import functools
    blines = [b[1] - b[0] for b in blocks]
    pref = [0]
    for b in blocks:
        pref.append(pref[-1] + (b[1] - b[0]))
    defs_at = {}
    for name, (d, l) in span.items():
        defs_at.setdefault(d, []).append((name, l))

    NEG = float("-inf")
    f = [NEG] * (nb + 1)
    f[0] = 0
    choice = [None] * (nb + 1)
    for j in range(1, nb + 1):
        i = j - 1
        while i >= 0 and pref[j] - pref[i] <= limit:
            if f[i] != NEG:
                cont = 0
                for d in range(i, j):
                    for (name, l) in defs_at.get(d, []):
                        if l <= j - 1:
                            cont += 1
                val = f[i] + cont
                if val > f[j]:
                    f[j] = val
                    choice[j] = i
            i -= 1
    total = len(privates)
    if f[nb] == NEG:
        print(f"{path}: NO partition with parts <= {limit} lines exists (an atomic block exceeds the limit)")
        return
    cuts = []
    j = nb
    while j > 0:
        i = choice[j]
        cuts.append((i, j))
        j = i
    cuts.reverse()
    promoted = total - f[nb]
    sizes = [pref[j] - pref[i] for (i, j) in cuts]
    print(f"{path}: minimal promotions for all parts <= {limit}: "
          f"{promoted} of {total} privates; {len(cuts)} parts, sizes {sizes}")


print("\n=== DP: minimal visibility promotions for a full <=1100-line split ===")
for (p, a, b, atomic) in FILES:
    min_promotions(p, a, b, atomic)


print("\n=== cheapest balanced 2-way cut (both parts >= 800 lines) ===")
for (p, a, b, atomic) in FILES:
    lines = Path(p).read_text(encoding="utf-8").split("\n")
    blocks = parse_blocks(lines, a, b)
    for (lo, hi) in atomic:
        merged, acc = [], None
        for blk in blocks:
            if lo <= blk[0] < hi:
                if acc is None:
                    acc = [blk[0], blk[1], "atomic", f"s@{lo}", False]
                else:
                    acc[1] = blk[1]
            else:
                if acc is not None:
                    merged.append(acc); acc = None
                merged.append(blk)
        if acc is not None:
            merged.append(acc)
        blocks = merged

    def strip_comments(text):
        out, i, depth, n = [], 0, 0, len(text)
        while i < n:
            if text.startswith("/-", i):
                depth += 1; i += 2
            elif text.startswith("-/", i) and depth > 0:
                depth -= 1; i += 2
            elif depth == 0 and text.startswith("--", i):
                j = text.find("\n", i); i = n if j == -1 else j
            else:
                if depth == 0:
                    out.append(text[i])
                i += 1
        return "".join(out)

    texts = [strip_comments("\n".join(lines[blk[0]:blk[1]])) for blk in blocks]
    privates = {}
    for idx, blk in enumerate(blocks):
        if blk[4]:
            privates[blk[3]] = idx
        if blk[2] == "atomic":
            for m in re.finditer(r"private\s+(?:noncomputable\s+)?"
                                 r"(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s+"
                                 r"([A-Za-z0-9_.']+)", texts[idx]):
                privates[m.group(1)] = idx
    pats = {n: re.compile(r"(?<![A-Za-z0-9_.'])" + re.escape(n) + r"(?![A-Za-z0-9_'])")
            for n in privates}
    span = {}
    for name, didx in privates.items():
        last = didx
        for idx in range(didx + 1, len(blocks)):
            if pats[name].search(texts[idx]):
                last = idx
        span[name] = (didx, last)
    best = None
    for i in range(len(blocks) - 1):
        endline = blocks[i][1]
        p1, p2 = endline - a, b - endline
        if p1 < 800 or p2 < 800:
            continue
        names = [n for n, (d, l) in span.items() if d <= i < l]
        if best is None or len(names) < best[0]:
            best = (len(names), endline, p1, p2, names)
    if best:
        c, endline, p1, p2, names = best
        print(f"{p}: cost {c} at line {endline} (parts {p1}/{p2})")
        print(f"   hubs: {', '.join(sorted(names))}")
    else:
        print(f"{p}: no balanced cut position exists")
