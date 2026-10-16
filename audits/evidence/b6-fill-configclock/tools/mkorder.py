"""The B6 F3 order list (read-only): the upstream closure (TCSlib modules) of
WindowClock and of every module downstream of it, in topological order, root excluded.

Usage: python3 -I mkorder.py <repo root> <graph.py dir> <out>
"""
import os, sys
root, gdir, out = sys.argv[1:4]
sys.path.insert(0, gdir)
from graph import imports_of  # noqa: E402
mods = {}
for d, _, fs in os.walk(os.path.join(root, 'TCSlib')):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(d, f)
            mods[os.path.relpath(p, root)[:-5].replace(os.sep, '.')] = [i for i in imports_of(p) if i.startswith('TCSlib')]
T = 'TCSlib.Complexity.SpaceComplexity.WindowClock'
assert T in mods
rev = {}
for m, imps in mods.items():
    for i in imps: rev.setdefault(i, set()).add(m)
down, todo = set(), [T]
while todo:
    m = todo.pop()
    if m in down: continue
    down.add(m); todo.extend(rev.get(m, ()))
up, todo = set(), list(down)
while todo:
    m = todo.pop()
    if m in up: continue
    up.add(m); todo.extend(i for i in mods.get(m, ()) if i in mods)
up.discard('TCSlib')
indeg = {m: sum(1 for i in mods[m] if i in up) for m in up}
ready = sorted(m for m in up if indeg[m] == 0); order = []
while ready:
    m = ready.pop(0); order.append(m)
    for n in sorted(rev.get(m, ())):
        if n in indeg:
            indeg[n] -= 1
            if indeg[n] == 0: ready.append(n); ready.sort()
assert len(order) == len(up), 'cycle'
open(out, 'w').write('\n'.join(m.replace('.', '/') for m in order) + '\n')
print(f'{len(order)} modules: downstream of WindowClock {len(down - {"TCSlib"})}, upstream closure {len(order)}')
