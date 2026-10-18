"""Simulate the round-2 seam-layout route on the three tapes src, tbl, sm.

Each phase is the catalog row's transition table as defined in Build/Catalog.lean (skipTM,
skipBackTM, walkTM, transferMapTM at the identity with the blank residue, clearTM) or one of
the two leaves of the round-2 sketch (pairSkip, unarySplit). Phases are composed as
phaseHostTM does: a phase's `done` takes one stationary silent dispatch step to the next phase's
start; the last phase's `done` is the exit.  Checks: the endpoint, the exact time formula, the
first exit, the time's independence of everything but (a, v, q, r), and T <= 18 (|s| + 1).
"""
import itertools, sys

SRC, TBL, SM = 0, 1, 2

def pair_encode(a, r):
    out = []
    for b in a:
        out += [b, b]
    return out + [False, True] + r

def buf(w):
    return {i: b for i, b in enumerate(w)}

def rd(tape, pos):
    return tape.get(pos)  # None = blank

# Each row: (start_state, tr) where tr(state, reads) -> (writes{tape: Option[bool] or 'blank'}, moves{tape: int}, next)
BL = 'blank'

def skipTM(i):
    def tr(q, w):
        if q == 'run':
            return ({}, {i: 1}, 'run' if w[i] is not None else 'done')
        return ({}, {}, q)
    return ('run', tr)

def skipBackTM(i):
    def tr(q, w):
        if q == 'run':
            return ({}, {i: -1}, 'gap')
        if q == 'gap':
            return ({}, {i: -1}, 'back')
        if q == 'back':
            return ({}, {i: -1}, 'back') if w[i] is not None else ({}, {i: 1}, 'done')
        return ({}, {}, 'done')
    return ('run', tr)

def walkTM(src, moved, d):
    def tr(q, w):
        if q == 'run':
            mv = {j: d for j in moved}
            return ({}, mv, 'run' if w[src] is not None else 'done')
        return ({}, {}, q)
    return ('run', tr)

def transferTM(src, dst):
    # transferMapTM at extract = id, merge = fun _ s => s, rest = fun _ => none
    def tr(q, w):
        if q == 'sweep':
            if w[src] is not None:
                return ({dst: w[src]}, {dst: 1, src: 1}, 'sweep')
            return ({}, {src: -1, dst: -1}, 'rewind')
        if q == 'rewind':
            if w[src] is not None:
                return ({src: BL}, {src: -1, dst: -1}, 'rewind')
            return ({}, {src: 1, dst: 1}, 'done')
        return ({}, {}, 'done')
    return ('sweep', tr)

def clearTM(i):
    def tr(q, w):
        if q == 'sweep':
            if w[i] is not None:
                return ({}, {i: 1}, 'sweep')
            return ({}, {i: -1}, 'rewind')
        if q == 'rewind':
            if w[i] is not None:
                return ({i: BL}, {i: -1}, 'rewind')
            return ({}, {i: 1}, 'done')
        return ({}, {}, 'done')
    return ('sweep', tr)

def pairSkip(i):
    # leaf L1: aligned pairs; an equal pair continues, (false, true) exits one past it.
    def tr(q, w):
        if q == 'even':
            if w[i] is None:
                return ({}, {}, 'done')        # unreachable on pairEncode
            return ({}, {i: 1}, ('odd', w[i]))
        if isinstance(q, tuple):
            b = q[1]; c = w[i]
            if c == b:
                return ({}, {i: 1}, 'even')
            if b is False and c is True:
                return ({}, {i: 1}, 'done')
            return ({}, {}, 'done')            # unreachable on pairEncode
        return ({}, {}, 'done')
    return ('even', tr)

def unarySplit(src, sm):
    # leaf L2: move sm right twice; copy the 1s to sm in lockstep; at the 0, write it on sm
    # (sm stays) and blank it on src (src moves right).
    def tr(q, w):
        if q == 'sh0':
            return ({}, {sm: 1}, 'sh1')
        if q == 'sh1':
            return ({}, {sm: 1}, 'copy')
        if q == 'copy':
            if w[src] is True:
                return ({sm: True}, {src: 1, sm: 1}, 'copy')
            if w[src] is False:
                return ({sm: False, src: BL}, {src: 1}, 'done')
            return ({}, {}, 'done')            # unreachable
        return ({}, {}, 'done')
    return ('sh0', tr)

PHASES = [skipTM(SRC), skipBackTM(SRC), pairSkip(SRC), unarySplit(SRC, SM),
          walkTM(SM, [SM], -1), transferTM(SRC, TBL), skipBackTM(SRC), clearTM(SRC)]

def run(tapes, heads, limit=10**6):
    """Run the phase host; return (T, tapes, heads, trace of (phase, state))."""
    ph, q = 0, PHASES[0][0]
    t = 0
    while True:
        if q == 'done':
            if ph == len(PHASES) - 1:
                return t, tapes, heads
            ph, q = ph + 1, PHASES[ph + 1][0]   # one silent stationary dispatch step
            t += 1
            continue
        w = {j: rd(tapes[j], heads[j]) for j in range(3)}
        writes, moves, nq = PHASES[ph][1](q, w)
        for j, val in writes.items():
            if val == BL:
                tapes[j].pop(heads[j], None)
            else:
                tapes[j][heads[j]] = val
        for j, m in moves.items():
            heads[j] += m
        q = nq
        t += 1
        if t > limit:
            raise RuntimeError('no exit')

def words(maxlen):
    for L in range(maxlen + 1):
        for bits in itertools.product([False, True], repeat=L):
            yield list(bits)

def main():
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    maxq = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    n_inst = 0; worst = 0.0
    for a in words(maxlen):
        for v in words(maxlen):
            for q in range(maxq + 1):
                u = [True] * q + [False]
                s = pair_encode(a, u + v)
                n = len(s); h = 2 * len(a) + 2
                for r in range(n + 1):
                    T, tp, hd = run([buf(s), {}, {}], [r, 0, 0])
                    exp_T = 2 * n - r + 4 * h + 5 * q + 2 * len(v) + 23
                    assert T == exp_T, (a, v, q, r, T, exp_T)
                    assert tp[SRC] == {}, ('src', a, v, q, r, tp[SRC])
                    assert tp[TBL] == buf(v), ('tbl', a, v, q, r, tp[TBL])
                    assert tp[SM] == {i + 2: b for i, b in enumerate(u)}, ('sm', a, v, q, r)
                    assert hd == [0, 0, 0], ('heads', a, v, q, r, hd)
                    assert T <= 7 * n + 18 <= 18 * (n + 1)
                    worst = max(worst, T / (n + 1))
                    n_inst += 1
    print(f'instances={n_inst} all-pass; T = 2|s| - r + 4h + 5q + 2|v| + 23; max T/(|s|+1) = {worst:.3f}')

