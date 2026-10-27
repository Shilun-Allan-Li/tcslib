"""Stable topological re-sort of an order list over imports.py's JSON (python3 -I): each module is
emitted after its TCSlib imports, keeping the given order otherwise.
usage: stabletopo.py <imports.json> <order in> <order out>"""
import json, sys
mods = json.load(open(sys.argv[1]))
L = [l.strip() for l in open(sys.argv[2]) if l.strip()]
S = set(L); out = []; done = set()
def emit(m, stack=()):
    if m in done: return
    assert m not in stack, ('cycle', stack + (m,))
    for d in mods.get(m, []):
        if d in S: emit(d, stack + (m,))
    done.add(m); out.append(m)
for m in L: emit(m)
assert len(out) == len(L) and set(out) == S
moved = [m for i, m in enumerate(out) if L.index(m) != i]
open(sys.argv[3], 'w').write('\n'.join(out) + '\n')
print(len(out), 'modules;', len(moved), 'positions changed')
