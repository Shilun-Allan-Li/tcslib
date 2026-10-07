#!/usr/bin/env python3
"""E5 dead-code analysis: per file, the private declarations not transitively
referenced (in comment-stripped code) from any public declaration of that file.

Privates are file-scoped in Lean 4, so a file's publics are the only possible
entry points into its private family graph; a private outside the transitive
closure of the publics' references is dead. The fresh module sweep after
deletion is the authoritative over-deletion check (an accidentally deleted
live name fails elaboration immediately).
"""
import re
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


def strip_comments(text):
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


def parse_blocks(lines, body_start, body_end):
    starts = []
    depth = 0
    for i in range(body_start, body_end):
        ln = lines[i]
        if depth == 0 and ln and not ln[0].isspace():
            if any(ln.startswith(k) for k in START_KEYWORDS):
                starts.append(i)
        depth += ln.count("/-") - ln.count("-/")
        if depth < 0:
            depth = 0
    starts.append(body_end)
    raw = [(starts[j], starts[j + 1]) for j in range(len(starts) - 1)]
    blocks, pending = [], None
    for (a, b) in raw:
        first = lines[a]
        if first.startswith(("/--", "/-!", "/-", "--")):
            if pending is None:
                pending = a
            continue
        start = pending if pending is not None else a
        pending = None
        m = DECL_RE.match(first)
        if m:
            blocks.append((start, b, m.group(3), bool(m.group(1)), m.group(2)))
        else:
            blocks.append((start, b, None, False, None))
    return blocks


def dead_set(path, body_start, body_end):
    lines = Path(path).read_text(encoding="utf-8").split("\n")
    blocks = parse_blocks(lines, body_start, body_end)
    texts = [strip_comments("\n".join(lines[b[0]:b[1]])) for b in blocks]
    priv_idx = {b[2]: i for i, b in enumerate(blocks) if b[3] and b[2]}
    pats = {n: re.compile(r"(?<![A-Za-z0-9_.'])" + re.escape(n) + r"(?![A-Za-z0-9_'])")
            for n in priv_idx}
    refs = {i: set() for i in range(len(blocks))}  # block -> private names it uses
    for i, text in enumerate(texts):
        for n, d in priv_idx.items():
            if i != d and pats[n].search(text):
                refs[i].add(n)
    live = set()
    frontier = []
    for i, b in enumerate(blocks):
        if b[2] and not b[3]:  # public declaration
            frontier.extend(refs[i])
        elif b[2] is None:  # structural / variable / open blocks: treat as live roots
            frontier.extend(refs[i])
        elif b[3] and b[4] == "instance":
            # private instances are consumed by typeclass resolution without
            # any textual reference: always live roots, never dead candidates
            frontier.append(b[2])
            frontier.extend(refs[i])
    while frontier:
        n = frontier.pop()
        if n in live:
            continue
        live.add(n)
        frontier.extend(refs[priv_idx[n]])
    dead = [n for n in priv_idx if n not in live]
    dead_blocks = sorted((priv_idx[n] for n in dead))
    print(f"\n### {path}: {len(priv_idx)} privates, {len(live)} live, {len(dead)} dead")
    total = 0
    for i in dead_blocks:
        b = blocks[i]
        total += b[1] - b[0]
        print(f"  lines {b[0]+1}-{b[1]}: {b[2]}")
    print(f"  dead lines total (incl. docstrings): {total}")
    return [(blocks[i][0], blocks[i][1], blocks[i][2]) for i in dead_blocks]


FILES = [
    ("TCSlib/Complexity/ClassNP/EXP.lean", 64, 2534),
    ("TCSlib/Complexity/ClassNP/Nondeterminism.lean", 77, 2454),
    ("TCSlib/Complexity/ClassNP/NP.lean", 0, None),
    ("TCSlib/Complexity/ClassNP/Reductions.lean", 0, None),
    ("TCSlib/Complexity/ClassNP/TMSAT.lean", 92, 1908),
]

if __name__ == "__main__":
    for (p, a, b) in FILES:
        if b is None:
            n = len(Path(p).read_text(encoding="utf-8").split("\n"))
            a, b = 0, n
        dead_set(p, a, b)
