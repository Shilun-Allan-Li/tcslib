"""Union of several modules' downstream closures, topological order, root TCSlib excluded.
Usage: python3 -I mkdownmulti.py <repo root> <graph dir> <out> <module> [<module> ...]"""
import os, sys
root, gdir, out = sys.argv[1:4]
targets = sys.argv[4:]
sys.path.insert(0, gdir)
from graph import imports_of  # noqa: E402
mods = {}
for d, _, fs in os.walk(os.path.join(root, 'TCSlib')):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(d, f)
            mods[os.path.relpath(p, root)[:-5].replace(os.sep, '.')] = [i for i in imports_of(p) if i.startswith('TCSlib')]
rev = {}
for m, imps in mods.items():
    for i in imps: rev.setdefault(i, set()).add(m)
down, todo = set(), list(targets)
assert all(t in mods for t in targets)
while todo:
    m = todo.pop()
    if m in down: continue
    down.add(m); todo.extend(rev.get(m, ()))
down.discard('TCSlib')
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for i in sorted(mods[m]):
        if i in down: visit(i)
    order.append(m)
for m in sorted(down): visit(m)
open(out, 'w').write(''.join(m.replace('.', '/') + '\n' for m in order))
print(len(order))
