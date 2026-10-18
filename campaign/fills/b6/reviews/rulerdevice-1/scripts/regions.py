import re, sys
# usage: regions.py <diff>; base-line positions of every removed line and insertion point vs the
# B6-F5 brief's regions: (a) imports after base line 7; (b) homes at blank base lines 202, 228, 281;
# (c) the sorry lines 227, 270, 337; (d) appendices: the closer lines 215, 248, 312.
diff = open(sys.argv[1], encoding='utf-8').read().split('\n')
removable = {215: '(d) closer t1', 248: '(d) closer t2', 312: '(d) closer t3',
             227: '(c) body t1', 270: '(c) body t2', 337: '(c) body t3'}
insertable = {8: '(a) imports after 7', 202: '(b) home 202', 203: '(b) home 202',
              228: '(b) home 228', 229: '(b) home 228', 281: '(b) home 281', 282: '(b) home 281'}
for n, r in removable.items(): insertable.setdefault(n, r); insertable.setdefault(n + 1, r)
bad = 0; ol = None; pts = []
for l in diff:
    m = re.match(r'^@@ -(\d+)(?:,\d+)? \+(\d+)', l)
    if m: ol = int(m.group(1)); continue
    if ol is None or l.startswith('---') or l.startswith('+++'): continue
    if l.startswith('-'):
        pts.append(('removed', ol, removable.get(ol))); ol += 1
    elif l.startswith('+'):
        lab = removable.get(ol - 1) if pts and pts[-1][0] != 'inserted-before' and pts[-1][1] == ol - 1 else None
        if pts and pts[-1][0] == 'inserted-before' and pts[-1][1] == ol: lab = pts[-1][2]
        pts.append(('inserted-before', ol, lab or insertable.get(ol)))
    else:
        ol += 1
from itertools import groupby
for k, g in groupby(pts, key=lambda p: (p[0], p[1], p[2])):
    g = list(g); print(f'{k[0]:16} base line {k[1]} ({len(g)} lines): {k[2]}')
    if k[2] is None: bad += len(g)
print('removed', sum(p[0] == 'removed' for p in pts), 'added', sum(p[0] != 'removed' for p in pts),
      'outside owned regions:', bad)
