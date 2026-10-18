"""Reproduce gate 43 finding 1's counterexamples on the round-1 sketch with the actual row tables."""
import importlib.util, os
spec = importlib.util.spec_from_file_location('sim', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'sim_route_lib.py'))
sim = importlib.util.module_from_spec(spec); spec.loader.exec_module(sim)
SRC, TBL, SM = sim.SRC, sim.TBL, sim.SM
def run_row(row, tapes, heads):
    q, tr = row; t = 0
    while q != 'done':
        w = {j: tapes[j].get(heads[j]) for j in range(3)}
        writes, moves, q = tr(q, w)
        for j, val in writes.items():
            if val == sim.BL: tapes[j].pop(heads[j], None)
            else: tapes[j][heads[j]] = val
        for j, m in moves.items(): heads[j] += m
        t += 1
    return t
# (i) a = v = [], q = 0: s = [F, T, F]; head 3; skipBackTM, then one right step
s = sim.pair_encode([], [False]); tapes = [sim.buf(s), {}, {}]; heads = [3, 0, 0]
run_row(sim.skipBackTM(SRC), tapes, heads); heads[SRC] += 1
print('(i) s =', s, ' skipBack from 3 then right ->', heads[SRC])
for r in range(len(s) + 1):
    tapes = [sim.buf(s), {}, {}]; heads = [r, 0, 0]
    run_row(sim.skipBackTM(SRC), tapes, heads)
    print('    skipBack alone from', r, '->', heads[SRC])
# (ii) copyTM src -> tbl from the start of v (cell 3, right after the unary terminator)
def copyTM(src, dst):
    def tr(q, w):
        if q == 'sweep':
            if w[src] is not None:
                return ({dst: w[src]}, {dst: 1, src: 1}, 'sweep')
            return ({}, {src: -1, dst: -1}, 'rewind')
        if q == 'rewind':
            if w[src] is not None:
                return ({}, {src: -1, dst: -1}, 'rewind')
            return ({}, {src: 1, dst: 1}, 'done')
        return ({}, {}, 'done')
    return ('sweep', tr)
for v in ([], [True]):
    s = sim.pair_encode([], [False] + v)
    tapes = [sim.buf(s), {}, {}]; heads = [3, 0, 0]
    run_row(copyTM(SRC, TBL), tapes, heads)
    print('(ii) v =', v, ' copyTM from cell 3 -> src, tbl heads', heads[SRC], heads[TBL], ' tbl =', tapes[TBL])
# (iii) clearTM restores its head: from 0 on s, ends at 0
s = sim.pair_encode([True], [True, False, True]); tapes = [sim.buf(s), {}, {}]; heads = [0, 0, 0]
run_row(sim.clearTM(SRC), tapes, heads); print('(iii) clearTM from 0 ends at', heads[SRC], ' src =', tapes[SRC])
