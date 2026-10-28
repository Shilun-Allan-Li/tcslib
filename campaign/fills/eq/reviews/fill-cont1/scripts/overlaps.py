"""Lean process intervals logged in the delivery (TIMING lines, and the start=/end= pairs of the
evidence outputs), and any overlap between two of them (python3 -I; data only).  Screens are
Python and are listed separately.
usage: python3 -I overlaps.py <delivery root>"""
import os, re, sys
from datetime import datetime
root = sys.argv[1]
def t(s): return datetime.strptime(s, '%Y-%m-%dT%H:%M:%SZ')
iv = []
for dp, dn, fn in os.walk(root):
    for f in fn:
        p = os.path.join(dp, f); rel = os.path.relpath(p, root)
        if rel.startswith('runtime/') or rel.startswith('screens/') or 'screen' in f: continue
        try: T = open(p, encoding='utf-8').read()
        except Exception: continue
        for m in re.finditer(r'^TIMING (\S+) start=(\S+) end=(\S+) wall', T, re.M):
            iv.append((t(m.group(2)), t(m.group(3)), f'{rel}:{m.group(1).split("/")[-1]}'))
        if rel.endswith('.out') or rel.endswith('axiom-log.txt'):
            s = re.search(r'start=(\S+Z)', T); e = re.search(r'end=(\S+Z)', T)
            if s and e and 'TIMING' not in T: iv.append((t(s.group(1)), t(e.group(1)), rel))
seen = set(); u = []
for a in sorted(iv):
    k = (a[0], a[1], a[2].split(':')[-1])
    if k in seen: continue
    seen.add(k); u.append(a)
print('intervals', len(u), 'from', u[0][0], 'to', max(b for _, b, _ in u))
ov = [(x, y) for i, x in enumerate(u) for y in u[i + 1:] if y[0] < x[1] and x[0] < y[1]]
print('overlapping pairs (strict):', len(ov))
for x, y in ov[:20]: print('  ', x[2], x[0].time(), x[1].time(), '|', y[2], y[0].time(), y[1].time())
for f in ['screens/screen-before.start', 'screens/screen-after.start', 'checks/screen-after-323e3588.start']:
    p = os.path.join(root, f)
    if os.path.exists(p): print('screen', f, open(p).read().replace('\n', ' '))
