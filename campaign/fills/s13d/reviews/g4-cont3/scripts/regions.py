import re, sys
# usage: regions.py <diff> ; reports the base-line positions of every removed line and every insertion point
diff = open(sys.argv[1], encoding='utf-8').read().split('\n')
allowed = [(127, 1149, 'home (a), 127-1149 per gate 58 (the brief says 127-1147)'), (1190, 1194, 'rebalance status paragraph (b)'), (1207, 1207, 'rebalance body (b)'), (1230, 1236, 'extension status paragraph (c)'), (1247, 1247, 'extension body (c)')]
def region(n):
    for a, b, name in allowed:
        if a <= n <= b: return name
    return None
bad = 0; ol = None; added = 0; removed = 0; pts = []
for l in diff:
    m = re.match(r'^@@ -(\d+)(?:,\d+)? \+(\d+)', l)
    if m: ol = int(m.group(1)); continue
    if ol is None or l.startswith('---') or l.startswith('+++'): continue
    if l.startswith('-'):
        pts.append(('removed', ol, region(ol))); removed += 1; ol += 1
    elif l.startswith('+'):
        # insertion between base lines ol-1 and ol
        pts.append(('inserted-before', ol, region(ol) or region(ol - 1))); added += 1
    elif l.startswith(' ') or l == '':
        ol += 1
from itertools import groupby
for k, g in groupby(pts, key=lambda p: (p[0], p[2])):
    g = list(g)
    print(f'{k[0]:16} base lines {g[0][1]}..{g[-1][1]} ({len(g)} lines): {k[1]}')
    if k[1] is None: bad += 1
print(f'added {added}, removed {removed}, outside owned regions: {bad}')
