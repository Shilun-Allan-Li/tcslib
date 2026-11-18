"""closure.py <repo> <module>... : DFS post-order of TCSlib modules imported (transitively), roots last."""
import sys, re, os
repo = sys.argv[1]; roots = sys.argv[2:]
seen, order, ml = set(), [], set()
def imports(m):
    p = os.path.join(repo, m.replace('.', '/') + '.lean')
    out = []
    for l in open(p, encoding='utf-8'):
        s = l.strip()
        if s.startswith('import '):
            out.append(s.split()[1])
    return out
sys.setrecursionlimit(100000)
def visit(m):
    if m in seen: return
    seen.add(m)
    for i in imports(m):
        if i.startswith('TCSlib'): visit(i)
        elif i.startswith('Mathlib'): ml.add(i)
        else: ml.add(i)
    order.append(m)
for r in roots: visit(r)
open(os.environ.get('ORDER_OUT','order.txt'),'w').write('\n'.join(x.replace('.','/') for x in order)+'\n')
open(os.environ.get('ROOTS_OUT','roots.txt'),'w').write('\n'.join(sorted(x for x in ml if x.startswith('Mathlib')))+'\n')
print(len(order), len(ml), sorted(x for x in ml if not x.startswith('Mathlib')))
