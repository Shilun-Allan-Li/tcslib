"""Show the shared tiles behind a copy-screen pair (the v3 screen's own extraction and tiling,
copied from scripts/copy-text-screen-v3.py; python3 -I).
usage: python3 -I tiles.py <root> <target file> <target decl> <source file> <source decl>"""
import re, sys
root, fa, da, fb, db = sys.argv[1:6]
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
def get(f, name):
    t = strip(open(f'{root}/{f}', encoding='utf-8').read()); ms = list(DECL.finditer(t))
    for i, m in enumerate(ms):
        if m.group(3) == name:
            end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
            return re.sub(r'\s+', '', body(t[m.start():end]))
    raise SystemExit('not found ' + name)
ta, tb = get(fa, da), get(fb, db)
a, b, c, tiles = ta, tb, 0, []
while True:
    n, seg = lcs(b, a)
    if n < 25: break
    c += n; tiles.append(seg); a = a.replace(seg, '\x00', 1); b = b.replace(seg, '\x01', 1)
print(f'{da} ({len(ta)} chars) reproduces {db} ({len(tb)} chars): {c}/{len(tb)} = {c/len(tb):.0%}')
print(f'  source body: {tb}')
for s in tiles: print(f'  tile {len(s)}: {s}')
