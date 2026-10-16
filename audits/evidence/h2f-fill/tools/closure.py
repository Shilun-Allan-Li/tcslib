"""Upstream closure of one module (read-only). Usage: python3 -I closure.py <root> <graph dir> <module>"""
import os, sys
root, gdir, T = sys.argv[1:4]
sys.path.insert(0, gdir)
from graph import imports_of  # noqa: E402
def path(m): return os.path.join(root, m.replace('.', os.sep) + '.lean')
seen, todo = set(), [T]
while todo:
    m = todo.pop()
    if m in seen or not os.path.exists(path(m)): continue
    seen.add(m); todo.extend(i for i in imports_of(path(m)) if i.startswith('TCSlib'))
for m in sorted(seen): print(m)
