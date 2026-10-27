import os, re, sys
root, order_file, roots_file = sys.argv[1], sys.argv[2], sys.argv[3]
def imports(mod):
    p = os.path.join(root, mod.replace('.', '/') + '.lean')
    out = []
    for line in open(p, encoding='utf-8'):
        m = re.match(r'^import\s+(\S+)', line)
        if m: out.append(m.group(1))
    return out
start = 'TCSlib.Complexity.Diagonalization'
seen, stack = set(), [start]
while stack:
    m = stack.pop()
    if m in seen or not m.startswith('TCSlib'): continue
    seen.add(m); stack.extend(imports(m))
order = [l.strip() for l in open(order_file) if l.strip() and not l.startswith('#')]
mods = [o[:-5].replace('/', '.') if o.endswith('.lean') else o.replace('/', '.') for o in order]
print('closure', len(seen), 'order', len(mods), 'equal sets', set(mods) == seen)
pos = {m: i for i, m in enumerate(mods)}
bad = [(m, d) for m in mods for d in imports(m) if d.startswith('TCSlib') and pos.get(d, 10**9) > pos[m]]
print('topological violations', len(bad), bad[:5])
roots = sorted({d for m in mods for d in imports(m) if d.startswith('Mathlib')})
given = [l.strip() for l in open(roots_file) if l.strip()]
print('roots', len(roots), 'given', len(given), 'equal', roots == sorted(given))
print('NTimeHierarchy pos', pos.get('TCSlib.Complexity.Diagonalization.NTimeHierarchy'), 'NTimeDiagonalizer pos', pos.get('TCSlib.Complexity.Diagonalization.NTimeDiagonalizer'))
# upstream closure of NTimeDiagonalizer
up, st = set(), ['TCSlib.Complexity.Diagonalization.NTimeDiagonalizer']
while st:
    m = st.pop()
    if m in up or not m.startswith('TCSlib'): continue
    up.add(m); st.extend(imports(m))
print('upstream of owned (incl.)', len(up))
down = [m for m in mods if 'TCSlib.Complexity.Diagonalization.NTimeDiagonalizer' in imports(m)]
print('direct importers of owned', down)
