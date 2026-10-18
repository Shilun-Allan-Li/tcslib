"""Phase-by-phase check of the round-2 route against each cited `_run_ofCfg` contract.

For every instance, run the phases one at a time (dispatch = 1 step), and at each phase start
check the cited contract's hypothesis literally (as stated in Build/Catalog.lean), then check that
the phase's exit time and endpoint are the contract's. The leaves' intended contracts are checked
the same way.
"""
import importlib.util, itertools, sys, os
spec = importlib.util.spec_from_file_location('sim', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'sim_route_lib.py'))
sim = importlib.util.module_from_spec(spec); spec.loader.exec_module(sim)
SRC, TBL, SM = sim.SRC, sim.TBL, sim.SM

def bt(w, p):
    return w[p] if 0 <= p < len(w) else None

def run_phase(idx, tapes, heads):
    start, tr = sim.PHASES[idx]
    q = start; t = 0
    while q != 'done':
        w = {j: tapes[j].get(heads[j]) for j in range(3)}
        writes, moves, nq = tr(q, w)
        for j, val in writes.items():
            if val == sim.BL: tapes[j].pop(heads[j], None)
            else: tapes[j][heads[j]] = val
        for j, m in moves.items(): heads[j] += m
        q = nq; t += 1
    return t

def check(a, v, q, r):
    u = [True] * q + [False]
    s = sim.pair_encode(a, u + v); n = len(s); h = 2 * len(a) + 2
    tapes = [sim.buf(s), {}, {}]; heads = [r, 0, 0]
    total = 0
    def tape(j, p): return tapes[j].get(p)
    # 1. skipTM src, w = s.drop r
    w = s[r:]; pos = heads[SRC]
    assert all(tape(SRC, pos + p) == bt(w, p) for p in range(0, len(w) + 1))
    t = run_phase(0, tapes, heads); assert t == len(w) + 1 and heads[SRC] == pos + len(w) + 1 == n + 1
    total += t + 1
    # 2. skipBackTM src, u = s
    U = s; pos = heads[SRC]
    assert all(tape(SRC, pos - len(U) - 1 + p) == bt(U, p) for p in range(-1, len(U) + 1))
    t = run_phase(1, tapes, heads); assert t == len(U) + 3 and heads[SRC] == pos - len(U) - 1 == 0
    total += t + 1
    # 3. leaf L1 pairSkip: from cell 0 of pairEncode a _, exactly 2|a|+2 steps, head at 2|a|+2, nothing written
    before = [dict(x) for x in tapes]
    t = run_phase(2, tapes, heads); assert t == h and heads == [h, 0, 0] and tapes == before
    total += t + 1
    # 4. leaf L2 unarySplit: q+3 steps; src head h+q+1 with cell h+q blanked; sm holds u from 2, head q+2
    t = run_phase(3, tapes, heads)
    assert t == q + 3 and heads == [h + q + 1, 0, q + 2]
    assert tapes[SRC] == {i: b for i, b in enumerate(s) if i != h + q}
    assert tapes[SM] == {i + 2: b for i, b in enumerate(u)}
    total += t + 1
    # 5. walkTM sm {sm} neg, w = u.reverse
    W = list(reversed(u)); pos = heads[SM]
    assert all(tape(SM, pos - p) == bt(W, p) for p in range(0, len(W) + 1))
    t = run_phase(4, tapes, heads); assert t == len(W) + 1 and heads[SM] == pos - (len(W) + 1) == 0
    total += t + 1
    # 6. transferTM src tbl, w = v (cell -1 is the blanked terminator)
    pos = heads[SRC]; tpos = heads[TBL]; tbl_before = dict(tapes[TBL])
    assert all(tape(SRC, pos + p) == bt(v, p) for p in range(-1, len(v) + 1))
    t = run_phase(5, tapes, heads); assert t == 2 * len(v) + 2 and heads[SRC] == pos and heads[TBL] == tpos
    assert all(tape(SRC, pos + p) is None for p in range(len(v)))
    assert tapes[TBL] == sim.buf(v)
    total += t + 1
    # 7. skipBackTM src, u = s.take (h + q)
    U = s[:h + q]; pos = heads[SRC]
    assert pos == h + q + 1
    assert all(tape(SRC, pos - len(U) - 1 + p) == bt(U, p) for p in range(-1, len(U) + 1))
    t = run_phase(6, tapes, heads); assert t == len(U) + 3 and heads[SRC] == 0
    total += t + 1
    # 8. clearTM src, w = s.take (h + q)
    pos = heads[SRC]
    assert all(tape(SRC, pos + p) == bt(U, p) for p in range(-1, len(U) + 1))
    t = run_phase(7, tapes, heads); assert t == 2 * len(U) + 2 and heads[SRC] == 0
    total += t
    assert tapes[SRC] == {} and tapes[TBL] == sim.buf(v) and tapes[SM] == {i + 2: b for i, b in enumerate(u)}
    assert heads == [0, 0, 0]
    assert total == 2 * n - r + 4 * h + 5 * q + 2 * len(v) + 23
    return 1

maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 3
maxq = int(sys.argv[2]) if len(sys.argv) > 2 else 4
cnt = 0
for a in sim.words(maxlen):
    for v in sim.words(maxlen):
        for q in range(maxq + 1):
            n = 2 * len(a) + 2 + q + 1 + len(v)
            for r in range(n + 1):
                cnt += check(a, v, q, r)
print(f'instances={cnt}: every phase start meets its cited contract hypothesis; every phase time and endpoint is the contract\'s; total = 2|s| - r + 4h + 5q + 2|v| + 23')
