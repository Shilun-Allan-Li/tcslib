# Extended order: the issued order.txt with every TCSlib module of its import closure (and of the
# owned file's new imports) inserted before its first consumer (stable DFS, post-order).
# Also prints the Mathlib roots (distinct `import Mathlib...` lines) of the extended list.
import re, sys
F = '/home/user/fill/'
order = [l.strip() for l in open(sys.argv[1]) if l.strip()]
def imps(m):
    t, ml = [], []
    for l in open(F + m + '.lean'):
        mm = re.match(r'^import\s+(\S+)', l)
        if mm:
            x = mm.group(1)
            if x.startswith('TCSlib'): t.append(x.replace('.', '/'))
            elif x.startswith('Mathlib'): ml.append(x)
    return t, ml
seen, out, roots = set(), [], set()
def visit(m, stack=()):
    if m in seen: return
    if m in stack: sys.exit(f'cycle at {m}')
    t, ml = imps(m)
    roots.update(ml)
    for i in t: visit(i, stack + (m,))
    seen.add(m); out.append(m)
for m in order: visit(m)
open(sys.argv[2], 'w').write('\n'.join(out) + '\n')
open(sys.argv[3], 'w').write('\n'.join(sorted(roots)) + '\n')
new = [m for m in out if m not in set(order)]
print(f'issued {len(order)}; extended {len(out)}; inserted {len(new)}; roots {len(roots)}')
for m in new: print('  +', m)
# order preserved?
pos = {m: i for i, m in enumerate(out)}
print('issued relative order preserved:', all(pos[a] < pos[b] for a, b in zip(order, order[1:])))
