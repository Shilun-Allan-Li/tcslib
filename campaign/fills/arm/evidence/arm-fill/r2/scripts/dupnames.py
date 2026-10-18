"""Same-file blind spot of the copy screen: it skips a pair when (file label, short name)
coincide, so two declarations with the same short name in ONE file (e.g. in different
namespaces) are never compared. List such names in the added files (bodies >= 60 chars, the
screen's floor) and compare each such group's bodies with the screen's own tiling.
usage: python3 -I dupnames.py <labels.tsv> <added.txt> <screen-root>"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore import strip_keep_lines, DECL, body
labels, added, sroot = sys.argv[1:4]
new = {l.strip() for l in open(added) if l.strip()}
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
groups = 0; hits = 0
for l in open(labels, encoding='utf-8'):
    flat, path, _ = l.rstrip('\n').split('\t')
    if path not in new: continue
    t = strip_keep_lines(open(os.path.join(sroot, flat), encoding='utf-8').read())
    ms = list(DECL.finditer(t)); by = {}
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        kind = 'proof' if m.group(2) in ('theorem', 'lemma') else 'term'
        bd = re.sub(r'\s+', '', body(t[m.start():end]))
        if len(bd) >= 60: by.setdefault((m.group(3), kind), []).append((t.count('\n', 0, m.start()) + 1, bd))
    for (n, k), v in by.items():
        if len(v) < 2: continue
        groups += 1
        for i in range(len(v)):
            for j in range(len(v)):
                if i == j: continue
                sh = tiled(v[j][1], v[i][1])
                if sh >= 60 and 2 * sh >= len(v[j][1]):
                    hits += 1
                    print(f'{path}: {n} (line {v[i][0]}) reproduces {n} (line {v[j][0]}): {sh}/{len(v[j][1])}')
        print(f'group {path}: {n} [{k}] at lines {[x[0] for x in v]}')
print(f'same-name groups in one added file (body >= 60): {groups}; directed hits the screen cannot see: {hits}')
