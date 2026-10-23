"""upclosure.py <graph dir> <repo> <module>  -> upstream closure (TCSlib modules) of module in the worktree, one per line, topological."""
import os, sys
gdir, root, target = sys.argv[1:4]
sys.path.insert(0, gdir)
from graph import imports_of
mods = {}
for d, _, fs in os.walk(os.path.join(root, 'TCSlib')):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(d, f)
            mods[os.path.relpath(p, root)[:-5].replace(os.sep, '.')] = [i for i in imports_of(p) if i.startswith('TCSlib')]
seen, order = set(), []
def visit(m):
    if m in seen: return
    seen.add(m)
    for i in sorted(mods[m]): visit(i)
    order.append(m)
visit(target)
for m in order: print(m)
