"""Upstream and downstream import closures of a module, from imports.py's JSON (python3 -I).
usage: python3 -I closure.py <imports.json> <module> [<order list>]"""
import json, sys
mods = json.load(open(sys.argv[1])); m = sys.argv[2]
def up(m, seen=None):
    seen = set() if seen is None else seen
    for d in mods.get(m, []):
        if d not in seen: seen.add(d); up(d, seen)
    return seen
U = up(m)
D = {x for x in mods if m in up(x)}
print(f'{m}: upstream {len(U)} TCSlib modules; downstream {len(D)}: {sorted(D)}')
for probe in ['TCSlib/Complexity/TuringMachine/Build/InterpreterStartup', 'TCSlib/Complexity/TuringMachine/NDCodeSimulator']:
    print(f'  {probe}: in upstream {probe in U}; in downstream {probe in D}')
if len(sys.argv) > 3:
    order = [l.strip() for l in open(sys.argv[3]) if l.strip()]
    S = set(order)
    print(f'order list: {len(order)} modules; upstream within it: {len(U & S)}/{len(U)}; missing from it: {sorted(U - S)}')
    print(f'order-list modules outside the upstream closure and not the module itself: {sorted(S - U - {m})}')
    # import-closed and topologically ordered?
    pos = {x: i for i, x in enumerate(order)}
    bad = [(x, d) for x in order for d in mods.get(x, []) if d not in pos or pos[d] > pos[x]]
    print(f'order list import-closed and topological: {not bad} {bad[:5]}')
    fac = 'TCSlib/Complexity/Diagonalization'
    if fac in mods:
        F = up(fac) | {fac}
        print(f'facade {fac}: closure {len(F)}; order list == facade closure: {S == F}; diff {sorted(S ^ F)[:10]}')
