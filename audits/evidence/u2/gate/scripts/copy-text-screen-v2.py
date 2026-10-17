"""Text-level copy screen for retrofit deliveries, v2 (path-keyed).

Identical to audits/evidence/retrofit/copy-text-screen.py (v1) except in how files are keyed.
v1 keyed each declaration by its file's *basename* and skipped a pair when (basename, name)
coincided, so two files with the same basename in different directories (e.g. Codec/Machine.lean
and ExpBFS/Machine.lean) were never compared on equal declaration names. v2 keys each declaration
by its file's repository-relative path (normalized; a path listed twice is screened once) and
skips a pair only when (path, name) coincide. Labels: a file is printed by its basename when that
basename is unique in the argument list, else by its repository-relative path. Hence, when all
basenames in the argument list are distinct, v2's output is byte-identical to v1's.

For the given Lean files it lists every like-kind pair (proof vs proof, term vs term) in which one
declaration reproduces at least half of another's extracted body (at least 60 characters, greedy
tiling with blocks of at least 25), within a file and across the given files. It also prints the
total reproduced text. Run it before and after a change: a pair present after but not before is
new duplication; inlining a deleted copy into a consumer shows up as such a pair.
Usage: python3 -I copy-text-screen-v2.py <repo-root> <file.lean> [<file.lean> ...]
"""
import os, re, sys
root, files = sys.argv[1], sys.argv[2:]
paths = list(dict.fromkeys(os.path.normpath(f) for f in files))
nbase = {}
for p in paths: nbase[os.path.basename(p)] = nbase.get(os.path.basename(p), 0) + 1
label = lambda p: os.path.basename(p) if nbase[os.path.basename(p)] == 1 else p
def strip(src):
    out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        out.append(src[i]); i += 1
    return ''.join(out)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:(?:noncomputable|private|protected)\s+)*)"
                  r"(def|theorem|lemma|abbrev|instance|structure|inductive)\s+(\S+)", re.M)
def body(b):
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif b.startswith(':=', i) and d == 0: return b[i + 2:]
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif d == 0 and (ch == '|' or re.match(r'\bwhere\b', b[i:i + 6])): return b[i:]
    return ''
def lcs(a, b):
    lo, hi, best = 0, min(len(a), len(b)), ''
    while lo < hi:
        mid = (lo + hi + 1) // 2
        subs = {b[i:i + mid] for i in range(len(b) - mid + 1)}
        hit = next((a[i:i + mid] for i in range(len(a) - mid + 1) if a[i:i + mid] in subs), None)
        if hit is not None: lo, best = mid, hit
        else: hi = mid - 1
    return lo, best
def tiled(a, b):
    c = 0
    while True:
        n, seg = lcs(a, b)
        if n < 25: return c
        c += n; a = a.replace(seg, '\x00', 1); b = b.replace(seg, '\x01', 1)
grams = lambda x: {x[i:i + 25] for i in range(len(x) - 24)}
decls = []
for p in paths:
    t = strip(open(f'{root}/{p}', encoding='utf-8').read()); ms = list(DECL.finditer(t))
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        kind = 'proof' if m.group(2) in ('theorem', 'lemma') else 'term'
        bd = re.sub(r'\s+', '', body(t[m.start():end]))
        if len(bd) >= 60: decls.append((p, m.group(3), kind, bd, grams(bd)))
pairs = []; total = 0
for (fa, a, ka, ta, ga) in decls:
    for (fb, b, kb, tb, gb) in decls:
        if (fa, a) == (fb, b) or ka != kb or not (ga & gb): continue
        sh = tiled(tb, ta)
        if sh >= 60 and 2 * sh >= len(tb):
            pairs.append((sh / len(tb), sh, len(tb), f'{label(fa)}::{a}', f'{label(fb)}::{b}')); total += sh
pairs.sort(reverse=True)
print(f"declarations screened: {len(decls)}; copy pairs (target reproduces >= half of source): {len(pairs)}; reproduced text: {total:,} chars")
for frac, sh, ln, a, b in pairs:
    print(f"   {a}  reproduces  {b}: {sh}/{ln} = {frac:.0%}")
