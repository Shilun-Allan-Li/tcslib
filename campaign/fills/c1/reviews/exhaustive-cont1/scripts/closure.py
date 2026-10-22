"""Import closures of TCSlib modules in a tree.
usage: python3 -I closure.py <tree> up|down <module path, e.g. TCSlib/Complexity/ClassNP/ExhaustiveReplay> [more ...]
Prints the closure (excluding the root `TCSlib`), in a topological (dependency) order."""
import os, re, sys
root, mode, targets = sys.argv[1], sys.argv[2], sys.argv[3:]
mods = {}
for d, _, fs in os.walk(os.path.join(root, 'TCSlib')):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(d, f)
            imps = []
            for line in open(p, encoding='utf-8'):
                m = re.match(r'^import\s+(TCSlib\S*)', line.strip())
                if m: imps.append(m.group(1).replace('.', '/'))
            mods[os.path.relpath(p, root)[:-5]] = imps
if os.path.exists(os.path.join(root, 'TCSlib.lean')):
    mods['TCSlib'] = [re.match(r'^import\s+(\S+)', l).group(1).replace('.', '/') for l in open(os.path.join(root, 'TCSlib.lean'), encoding='utf-8') if l.startswith('import ')]
rev = {}
for m, imps in mods.items():
    for i in imps: rev.setdefault(i, set()).add(m)
nxt = (lambda m: mods.get(m, [])) if mode == 'up' else (lambda m: rev.get(m, ()))
seen, todo = set(), list(targets)
while todo:
    m = todo.pop()
    if m in seen: continue
    seen.add(m); todo.extend(nxt(m))
if mode == 'up': seen -= set(targets)
seen.discard('TCSlib')
order, vis = [], set()
def visit(m):
    if m in vis: return
    vis.add(m)
    for i in sorted(mods.get(m, [])):
        if i in seen: visit(i)
    order.append(m)
for m in sorted(seen): visit(m)
print('\n'.join(order))
