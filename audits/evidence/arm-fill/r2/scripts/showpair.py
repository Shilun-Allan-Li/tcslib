"""Inspection aid: for pair ids of pairs.tsv, print each side's declaration header (comment-
stripped, whitespace-compressed, cut at the body) and the shared tiles (the screen's own greedy
tiling, blocks >= 25 whitespace-free chars) of the pair's largest directed hit.
usage: python3 -I showpair.py <pairs.tsv> <labels.tsv> <screen-root> <cap> pid [pid ...]"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore import strip_keep_lines, DECL, body
ptsv, labels, sroot, cap = sys.argv[1:5]; cap = int(cap); want = sys.argv[5:]
flat = {}
for l in open(labels, encoding='utf-8'):
    a, p, _ = l.rstrip('\n').split('\t'); flat[p] = a
cache = {}
def decl(path, name):
    if path not in cache:
        t = strip_keep_lines(open(os.path.join(sroot, flat[path]), encoding='utf-8').read())
        ms = list(DECL.finditer(t)); d = {}
        for i, m in enumerate(ms):
            end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
            d.setdefault(m.group(3), t[m.start():end])
        cache[path] = d
    return cache[path].get(name, '')
def lcs(a, b):
    lo, hi, best = 0, min(len(a), len(b)), ''
    while lo < hi:
        mid = (lo + hi + 1) // 2
        subs = {b[i:i + mid] for i in range(len(b) - mid + 1)}
        hit = next((a[i:i + mid] for i in range(len(a) - mid + 1) if a[i:i + mid] in subs), None)
        if hit is not None: lo, best = mid, hit
        else: hi = mid - 1
    return lo, best
def tiles(a, b):
    out = []
    while True:
        n, seg = lcs(a, b)
        if n < 25: return out
        out.append(seg); a = a.replace(seg, '\x00', 1); b = b.replace(seg, '\x01', 1)
rows = {}
for l in open(ptsv, encoding='utf-8'):
    c = l.rstrip('\n').split('\t'); rows[c[0]] = c
for pid in want:
    c = rows[pid]
    A, B = (c[2], c[3]), (c[7], c[8])
    sa, sb = decl(*A), decl(*B)
    def head(s):
        h = s[:len(s) - len(body(s))] if body(s) else s
        return re.sub(r'\s+', ' ', h).strip()[:300]
    ba, bb = re.sub(r'\s+', '', body(sa)), re.sub(r'\s+', '', body(sb))
    print(f'=== {pid} [{c[1]}] {c[12]}')
    print(f'  A {A[0].replace("TCSlib/Complexity/","")}:{c[4]} :: {head(sa)}')
    print(f'  B {B[0].replace("TCSlib/Complexity/","")}:{c[9]} :: {head(sb)}')
    ts = tiles(ba, bb); shown = 0
    print(f'  shared tiles ({sum(map(len, ts))} chars; A body {len(ba)}, B body {len(bb)}):')
    for t in ts:
        if shown >= cap: print('   ...'); break
        print('   |', t[:cap - shown]); shown += len(t)
