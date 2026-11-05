"""Upstream and downstream import closures of a module, from imports.py's JSON (python3 -I).
usage: python3 -I closure2.py <imports.json> <module> [<order list>] [<probe module> ...]"""
import json, sys
mods = json.load(open(sys.argv[1])); m = sys.argv[2]
order = sys.argv[3] if len(sys.argv) > 3 and sys.argv[3].endswith('.txt') else None
probes = sys.argv[4:] if order else sys.argv[3:]
def up(m, seen=None):
    seen = set() if seen is None else seen
    for d in mods.get(m, []):
        if d not in seen: seen.add(d); up(d, seen)
    return seen
U = up(m)
D = sorted(x for x in mods if m in up(x))
print(f'{m}: upstream {len(U)} TCSlib modules; downstream {len(D)}: {D}')
for p in probes: print(f'  {p}: in upstream {p in U}; in downstream {p in D}')
if order:
    O = [l.strip() for l in open(order) if l.strip() and not l.startswith('#')]
    S = set(O)
    print(f'order list: {len(O)} modules; upstream within it: {len(U & S)}/{len(U)}; missing: {sorted(U - S)}')
    pos = {x: i for i, x in enumerate(O)}
    bad = [(x, d) for x in O for d in mods.get(x, []) if d not in pos or pos[d] > pos[x]]
    print(f'order list import-closed and topological: {not bad} {bad[:5]}')
    print(f'downstream modules in the order list: {[d for d in D if d in S]}; not in it: {[d for d in D if d not in S]}')
