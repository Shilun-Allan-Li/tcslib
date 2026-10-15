"""Below-floor entries: tiled overlap (the screen's own greedy tiling, blocks >= 25 chars, no
60-char floor) between a declaration and its named original; prints body sizes and lines.
usage: python3 -I manualtile.py <labels> <screen-root> <spec.tsv> [<checkout>]   (spec: class, copy path, copy
decl, original path, original decl, group, note); output = manual.tsv rows: class, path, decl, shared, group, note"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore import strip_keep_lines, DECL, body
labels, sroot, spec = sys.argv[1:4]
checkout = sys.argv[4] if len(sys.argv) > 4 else None  # fallback for originals outside the screen population
flat = {}
for l in open(labels, encoding='utf-8'):
    a, p, _ = l.rstrip('\n').split('\t'); flat[p] = a
cache = {}
def get(path, name):
    if path not in cache:
        src = os.path.join(sroot, flat[path]) if path in flat else os.path.join(checkout, path)
        t = strip_keep_lines(open(src, encoding='utf-8').read())
        ms = list(DECL.finditer(t)); d = {}
        for i, m in enumerate(ms):
            end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
            seg = t[m.start():end]
            d.setdefault(m.group(3), (t.count('\n', 0, m.start()) + 1, re.sub(r'\s+', '', body(seg)), sum(1 for x in seg.split('\n') if x.strip())))
        cache[path] = d
    return cache[path][name]
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
for l in open(spec, encoding='utf-8'):
    if l.startswith('#') or not l.strip(): continue
    c = l.rstrip('\n').split('\t')
    (la, ba, ca), (lb, bb, cb) = get(c[1], c[2]), get(c[3], c[4])
    sh = tiled(bb, ba)
    # D1 and D6 are identical up to bound-variable names, which breaks the 25-character tiles;
    # their shared text is recorded as the whole body (named override, stated in the log)
    shx = len(ba) if c[2] in ('InWin', 'synOK') else sh
    print(f'{c[0]}\t{c[1]}\t{c[2]}\t{shx}\t{c[5]}\ttiled {sh}; copy line {la}, {ca} code lines, body {len(ba)}; original {c[3]}::{c[4]} line {lb}, body {len(bb)}; {c[6]}')
