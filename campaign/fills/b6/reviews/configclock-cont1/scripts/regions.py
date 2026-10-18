import re, sys
# usage: regions.py <diff>: base-line positions of every removed line and insertion point vs the
# B6-F3 cont1 brief's regions: (a) the home, base lines 143-224 (insertions before 143..225);
# (b) the target's sorry, base line 310; (c) the appendix paragraph, base lines 269-278
# (insertions before 269..279).
diff = open(sys.argv[1], encoding='utf-8').read().split('\n')
def region_removed(n):
    if 143 <= n <= 224: return '(a) home'
    if n == 310: return '(b) body'
    if 269 <= n <= 278: return '(c) appendix'
def region_ins(n):  # inserted immediately before base line n
    if 143 <= n <= 225: return '(a) home'
    if n in (310, 311): return '(b) body'
    if 269 <= n <= 279: return '(c) appendix'
pts = []; ol = None
for l in diff:
    m = re.match(r'^@@ -(\d+)(?:,\d+)? \+(\d+)', l)
    if m: ol = int(m.group(1)); continue
    if ol is None or l.startswith('---') or l.startswith('+++'): continue
    if l.startswith('-'): pts.append(('removed', ol, region_removed(ol))); ol += 1
    elif l.startswith('+'): pts.append(('inserted-before', ol, region_ins(ol)))
    else: ol += 1
from itertools import groupby
bad = 0
for k, g in groupby(pts, key=lambda p: (p[0], p[2])):
    g = list(g); print(f'{k[0]:16} base line {g[0][1]}..{g[-1][1]} ({len(g)} lines): {k[1]}')
    if k[1] is None: bad += len(g)
print('removed', sum(p[0] == 'removed' for p in pts), 'added', sum(p[0] != 'removed' for p in pts),
      'outside owned regions:', bad)
