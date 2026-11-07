"""newpairs.py <final screen> <base screen>: classify head-only pairs. A head-only pair is
'moved' when, after mapping each moved declaration back to its base name and file (the moves of
this fill), the pair existed in the base screen; otherwise 'new'."""
import re, sys
P = re.compile(r'^\s+(\S+)::(\S+)\s+reproduces\s+(\S+)::(\S+): (\d+)/(\d+) = (\d+)%')
def load(p):
    d = {}
    for l in open(p, encoding='utf-8'):
        m = P.match(l)
        if m: d[(m.group(1), m.group(2), m.group(3), m.group(4))] = (int(m.group(5)), int(m.group(6)), int(m.group(7)))
    return d
H = load(sys.argv[1]); B = load(sys.argv[2])
ren = {}
def back(f, n):
    if f == 'Primitives.lean' and (n.startswith('fwdMap') or n.startswith('FwdMap')):
        return ('Catalog.lean', 'a2_' + n.replace('fwdMap', 'map').replace('FwdMap', 'Map').replace('map_', 'map_'))
    if f == 'Primitives.lean' and n in ('polyHeads', 'polyHeads_bounds', 'poly_step', 'poly_space'):
        return ('Catalog.lean', 'f2_' + n)
    m = {'timedHeads': 'f2_condHeads', 'timed_control_heads': 'f2_control_heads',
         'timed_branch_heads': 'f2_branch_heads', 'timed_read_heads': 'f2_read_heads',
         'timed_ledger': 'f2_cond_ledger', 'timedCondTM_spaceUsed': 'f2_cond_space'}
    if f == 'Wrappers.lean' and n in m: return ('Catalog.lean', m[n])
    if f == 'Loop.lean' and n in ('segment_heads', 'seamed_space', 'loopCall_heads'):
        return ('Catalog.lean', 'f2_' + n)
    if f == 'Simulation.lean' and n == 'branchTM_spaceUsed': return ('Catalog.lean', 'f2_branch_space')
    return (f, n)
def fix_a2(f, n):
    # a2_ names in the base: a2_MapState, a2_mapAct, a2_mapTM, a2_map_move, a2_mapSetup_run ...
    if n.startswith('a2_map'): return (f, n)
    if n.startswith('a2_Map'): return (f, n)
    return (f, n)
moved = []; new = []
for k, v in H.items():
    if k in B: continue
    f1, n1 = back(k[0], k[1]); f2, n2 = back(k[2], k[3])
    if (f1, n1, f2, n2) in B: moved.append((k, v, (f1, n1, f2, n2)))
    else: new.append((k, v))
print(f'head pairs {len(H)}; base pairs {len(B)}; head-only {len(moved) + len(new)}: moved-and-renamed {len(moved)}, new {len(new)}')
for k, v in sorted(new, key=lambda t: -t[1][0]):
    print(f'NEW  {k[0]}::{k[1]} reproduces {k[2]}::{k[3]}: {v[0]}/{v[1]} = {v[2]}%')
for k, v, b in moved:
    print(f'MOVED {k[0]}::{k[1]} ~ {k[2]}::{k[3]} (base: {b[0]}::{b[1]} ~ {b[2]}::{b[3]}) {v[0]}/{v[1]}')
