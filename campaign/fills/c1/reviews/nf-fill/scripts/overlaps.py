"""Lean-run intervals from the worker's logs (START/END lines) and their pairwise overlaps (python3 -I).
usage: python3 -I overlaps.py <logs dir>"""
import os, re, sys
from datetime import datetime
d = sys.argv[1]; iv = []
for f in sorted(os.listdir(d)):
    if not f.endswith('.log'): continue
    starts = {}
    for l in open(os.path.join(d, f), encoding='utf-8', errors='replace'):
        m = re.match(r'^(START|END) (\S+) (\S+)', l)
        if not m: continue
        t = datetime.fromisoformat(m.group(2)); k = m.group(3)
        if m.group(1) == 'START': starts[k] = t
        elif k in starts: iv.append((starts.pop(k), t, f, k))
    for k, t in starts.items(): iv.append((t, None, f, k + ' (no END)'))
iv.sort(key=lambda x: x[0])
print('lean runs with START/END:', len(iv))
ov = []
done = [x for x in iv if x[1]]
for i, a in enumerate(done):
    for b in done[i + 1:]:
        if b[0] >= a[1]: break
        ov.append((a, b))
print('overlapping pairs:', len(ov))
for a, b in ov[:20]: print(f'  {a[2]}:{a[3]} {a[0].time()}-{a[1].time()}  ||  {b[2]}:{b[3]} {b[0].time()}-{b[1].time()}')
print('unfinished:', [(x[2], x[3]) for x in iv if not x[1]])
