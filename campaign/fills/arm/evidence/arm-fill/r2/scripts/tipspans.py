"""Spans (ledger.py rules) of the library side of every library pair, at the received tree (round-1
screen copies) and at the tip checkout; flags any difference.
usage: python3 -I tipspans.py <pairs.tsv> <labels> <screen-root> <checkout>"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore import strip_keep_lines, DECL, body
ptsv, labels, sroot, root = sys.argv[1:5]
flat = {}
for l in open(labels, encoding='utf-8'):
    a, p, _ = l.rstrip('\n').split('\t'); flat[p] = a
def spans(text):
    t = strip_keep_lines(text); ms = list(DECL.finditer(t)); d = {}
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        seg = t[m.start():end]; l0 = t.count('\n', 0, m.start()) + 1
        d.setdefault(m.group(3), (l0, l0 + seg.rstrip().count('\n')))
    return d
cache = {}
diff = 0; n = 0
for l in open(ptsv, encoding='utf-8'):
    c = l.rstrip('\n').split('\t')
    if c[1] != 'lib': continue
    p, nm = c[7], c[8]
    if p not in cache:
        cache[p] = (spans(open(os.path.join(sroot, flat[p]), encoding='utf-8').read()),
                    spans(open(os.path.join(root, p), encoding='utf-8').read()))
    a, b = cache[p][0].get(nm), cache[p][1].get(nm); n += 1
    if a != b:
        diff += 1; print(f'{c[0]} {p}::{nm}: received {a[0]}-{a[1]} tip {b[0]}-{b[1]}' if b else f'{c[0]} {p}::{nm}: missing at tip')
print(f'library-side spans compared: {n}; different at the tip: {diff}')
