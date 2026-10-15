"""Manual (below-floor) rows for one tree: for each spec row present at the tree, the screen's own
tiled overlap (blocks >= 25 chars, no 60-char floor) between the copy and its named original.
A row is emitted only if both ends exist at the tree and the row's `trees` field names the tree.
usage: python3 -I manualtile3.py <tree-root> <tree-name> <spec.tsv>
spec: class, copy path, copy decl, original path, original decl, group, trees (comma list), override, note
output (manual3 rows): class, path, decl, shared, group, note"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore3 import alldecls
root, tname, spec = sys.argv[1:4]
cache = {}
def get(p, n):
    if p not in cache:
        cache[p] = {}
        for d in alldecls(open(os.path.join(root, p), encoding='utf-8').read()): cache[p].setdefault(d['short'], d)
    return cache[p].get(n)
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
print('# class\tpath\tdecl\tshared\tgroup\tnote')
for l in open(spec, encoding='utf-8'):
    if l.startswith('#') or not l.strip(): continue
    c = l.rstrip('\n').split('\t')
    if tname not in c[6].split(','): continue
    a, b = get(c[1], c[2]), get(c[3], c[4])
    assert a and b, (c[1], c[2], c[3], c[4])
    sh = tiled(b['body'], a['body'])
    shx = a['chars'] if c[7] == 'body' else sh
    print(f"{c[0]}\t{c[1]}\t{c[2]}\t{shx}\t{c[5]}\ttiled {sh}; copy line {a['l0']}, {a['code']} code lines, body {a['chars']}; original {c[3]}::{c[4]} line {b['l0']}, body {b['chars']}; {c[8]}")
