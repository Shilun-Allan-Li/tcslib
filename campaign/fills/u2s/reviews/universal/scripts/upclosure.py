"""Upstream import closure of a module. Usage: python3 -I upclosure.py <graph dir> <repo root> <module> [<changed files...>]"""
import os, sys
gdir, root, target = sys.argv[1:4]
sys.path.insert(0, gdir)
from graph import imports_of
def path(m): return os.path.join(root, m.replace('.', '/') + '.lean')
up, todo = set(), [target]
while todo:
    m = todo.pop()
    if m in up: continue
    up.add(m)
    todo.extend(i for i in imports_of(path(m)) if i.startswith('TCSlib') and os.path.exists(path(i)))
print(len(up), 'modules in the upstream closure of', target, '(itself included)')
for m in sorted(up): print(' ', m)
for f in sys.argv[4:]:
    m = f[:-5].replace('/', '.')
    print('IN CLOSURE' if m in up else 'not in closure', f)
