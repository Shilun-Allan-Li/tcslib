import sys, os, re
# usage: closure.py <repo> <module>...  -> prints TCSlib modules in dependency (post-)order
repo = sys.argv[1]
seen = set(); order = []; mathlib = set()
def imports(m):
    p = os.path.join(repo, m.replace('.', '/') + '.lean')
    out = []
    with open(p) as f:
        for line in f:
            s = line.strip()
            if s.startswith('import '):
                out.append(s.split()[1])
    return out
def visit(m):
    if m in seen: return
    seen.add(m)
    for i in imports(m):
        if i.startswith('TCSlib'):
            visit(i)
        else:
            mathlib.add(i)
    order.append(m)
sys.setrecursionlimit(100000)
for m in sys.argv[2:]:
    visit(m)
mode = os.environ.get('MODE', 'order')
if mode == 'order':
    print('\n'.join(x.replace('.', '/') for x in order))
else:
    print('\n'.join(sorted(mathlib)))
