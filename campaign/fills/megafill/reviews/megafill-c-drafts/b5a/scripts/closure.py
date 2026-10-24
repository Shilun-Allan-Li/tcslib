"""Import closures over a TCSlib tree. Usage: closure.py <root> up|down <Module/Path> [...]
   up: the upstream closure (what it imports, transitively); down: every module that imports it."""
import os, re, sys
root, mode, targets = sys.argv[1], sys.argv[2], sys.argv[3:]
mods = {}
for dp, dn, fn in os.walk(os.path.join(root, 'TCSlib')):
    for f in fn:
        if f.endswith('.lean'):
            p = os.path.join(dp, f)
            m = os.path.relpath(p, root)[:-5]
            imps = []
            for line in open(p, encoding='utf-8'):
                mm = re.match(r'^import\s+(\S+)', line.strip())
                if mm and mm.group(1).startswith('TCSlib'):
                    imps.append(mm.group(1).replace('.', '/'))
            mods[m] = imps
if os.path.exists(os.path.join(root, 'TCSlib.lean')):
    mods['TCSlib'] = [mm.group(1).replace('.', '/') for line in open(os.path.join(root, 'TCSlib.lean'))
                      for mm in [re.match(r'^import\s+(\S+)', line.strip())] if mm]
rev = {}
for m, imps in mods.items():
    for i in imps: rev.setdefault(i, []).append(m)
def clos(start, g):
    seen, st = set(), list(start)
    while st:
        x = st.pop()
        for y in g.get(x, []):
            if y not in seen: seen.add(y); st.append(y)
    return seen
g = mods if mode == 'up' else rev
for t in targets:
    assert t in mods, t
c = clos(targets, g)
for m in sorted(c): print(m)
