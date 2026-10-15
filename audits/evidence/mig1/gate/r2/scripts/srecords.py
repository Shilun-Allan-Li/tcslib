"""Decision 2's records: for the eight citation specs proved at stage S, the batch from which each
is sorry-free. Read-only; a text scan, not a kernel check.

Usage: python3 -I srecords.py <unit.lean> <spec-probe tail.lean>

At S a citation spec's proof is its spec-probe proof (`MIG1Probe.spec_X`, with the probe's
`MIG1Probe.*` helpers it names). Its dependencies are the unit's declarations cited in that proof,
followed transitively through proved unit theorems (the four promotions are proved at S by their
unchanged home proofs and end the walk). A dependency that is still `sorry` at S is one of the 19
specs filled by F-A, F-B or F-C (the unit's 31 sorried statements minus the four promotions and
the eight); the spec is sorry-free from the last batch among its dependencies' batches.
"""
import re
import sys

unit = open(sys.argv[1], encoding='utf-8').read()
tail = open(sys.argv[2], encoding='utf-8').read()


def chunks(t):
    out = {}
    for c in re.split(r'\n(?=(?:/--|theorem |def |abbrev |private |noncomputable |instance |lemma ))', t):
        m = re.match(r'(?:/--(?:.|\n)*?-/\n)?(?:private |noncomputable )*(theorem|def|abbrev|lemma|instance)'
                     r' (\S+)', c)
        if m:
            out[m.group(2).replace('_root_.Turing.FinTM.', '')] = (
                m.group(1), c[m.end():], bool(re.search(r':= by\n  sorry\b', c)))
    return out


U, P = chunks(unit), chunks(tail)
PROMOTIONS = {'prependTM_computes', 'incFixedTM_computes', 'pairValidTM_computes', 'pairExtractTM_computes'}
EIGHT = ['callTM_run', 'redirectTM_runFrom', 'polyUnaryTM_computes', 'pairLenCheckTM_computes',
         'stripLastTM_computes', 'splitSolveTM_computes', 'splitSolveTM_spaceUsed',
         'splitSolveWithTM_computes']
BATCH = {'F-A': {'branchTM_spaceUsed', 'idTM_computes', 'ifEqTM_computes', 'condTM_computes_iff',
                 'timedCondTM_computes', 'timedCondTM_spaceUsed', 'pairDiagTM_computes',
                 'lengthBitsTM_computes', 'lengthBitsTM_spaceUsed'},
         'F-C': {'loopHostTM_contracts', 'loopHostTM_decides', 'loopHostTM_finds',
                 'loopHostTM_spaceUsed_le_budget', 'emitLoopTM_computes'},
         'F-B': {'polyUnaryTM_spaceUsed', 'unaryTokenTM_computes', 'appendBitTM_computes',
                 'pairMapSndTM_computes', 'pairMapSndTM_spaceUsed'}}
ORDER = ['S', 'F-A', 'F-C', 'F-B']  # integration order F-A, F-C, F-B
sorried = {n for n, (_, _, s) in U.items() if s and not n.startswith('MIG1Gate')}
later = sorried - PROMOTIONS - set(EIGHT)
assert later == set().union(*BATCH.values()), sorted(later ^ set().union(*BATCH.values()))
helpers = {n: b for n, (_, b, _) in P.items() if n.startswith('MIG1Probe.') and not n.startswith('MIG1Probe.spec_')}


def proof(n):
    if n in EIGHT:
        b = P['MIG1Probe.spec_' + n][1]
        return b + ''.join(hb for h, hb in helpers.items() if h in b)
    return U[n][1]


def deps(n, seen):
    body, res = proof(n), set()
    for m in U:
        if m == n or m.startswith('MIG1Gate') or not re.search(r'(?<![\w.])' + re.escape(m) + r"(?![\w'])", body):
            continue
        if m in later:
            res.add(m)
        elif m not in seen and U[m][0] in ('theorem', 'lemma') and m not in PROMOTIONS:
            seen.add(m)
            res |= deps(m, seen)
    return res


print(f'unit sorried statements: {len(sorried)}; promotions: {len(PROMOTIONS)}; the eight: {len(EIGHT)}; '
      f'filled later: {len(later)}')
for n in EIGHT:
    d = deps(n, set())
    b = max((next(k for k, v in BATCH.items() if x in v) for x in d), key=ORDER.index, default='S')
    print(f'{n}: proof supplied at S; sorry dependencies {sorted(d) or "none"}; sorry-free from {b}')
