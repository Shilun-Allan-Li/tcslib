import os, sys
# usage: upclosure.py <repo root> <graph dir> <module path without .lean>: TCSlib upstream closure
root, gdir, target = sys.argv[1:4]
sys.path.insert(0, gdir)
from graph import imports_of
def path(m): return os.path.join(root, m.replace('.', '/') + '.lean')
up, todo = set(), [target.replace('/', '.')]
while todo:
    m = todo.pop()
    for i in imports_of(path(m)):
        if i.startswith('TCSlib') and i not in up: up.add(i); todo.append(i)
print(len(up)); print('\n'.join(sorted(up)))
