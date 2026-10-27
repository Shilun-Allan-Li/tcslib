"""Seal the NDHost API PR's changed declarations (python3 -I): mkseal_nf3.py <NDHost.lean> <out.lean>.
Each changed region is wrapped in its own section, which makes the other-file TCSlib definitions
the changed code reaches locally irreducible and erases the four @[simp] TCSlib definitions of the
environment. The unchanged public declarations stay outside every seal; the one unchanged private
helper `wr_tape_append` is inside the first region (the writer's helpers and contracts)."""
import sys
src, out = sys.argv[1:3]
s = open(src, encoding='utf-8').read()
SEAL = ['Turing.moveInputPos', 'Turing.Cfg.inputSymbol', 'Turing.Cfg.workTapeSymbols', 'Turing.Cfg.init',
        'Turing.Action.apply', 'Turing.Action.mapState', 'Turing.Cfg.mapState', 'Turing.NDTM.stepWith',
        'Turing.NDTM.initCfg', 'Turing.NDTM.runWith', 'Turing.MultiTapeTM.toNDTM', 'Turing.MultiTapeTM.initCfg',
        'Turing.MultiTapeTM.runFrom', 'Turing.MultiTapeTM.step', 'Turing.FinTM.bufferTape', 'Turing.skipTM',
        'Turing.skipBackTM']
SIMPDEFS = ['Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg', 'Turing.NDTM.initCfg']
def block(n):
    return (f'\nsection NFSeal{n}\n-- seal: the other-file TCSlib definitions the changed code reaches, '
            'and the @[simp] ones erased\nattribute [-simp] ' + ' '.join(SIMPDEFS) + '\n'
            'attribute [local irreducible]\n' + ''.join('  ' + d + '\n' for d in SEAL) + '\n')
def endb(n): return f'\nend NFSeal{n}\n\n'
regions = [  # (start marker, end marker): the region is [start, end)
    ('/-- The configuration after writing the word `s`, in the writer state `q`, before testing the\n',
     '\nend Turing\n\n/-! ## The guess-then-run assembly'),
    ('/-- A writer\'s endpoint over a renamed configuration, through the renaming\'s field equations:\n',
     '/-- **Through the guess and the rewind.** Let the setup `P` run from its initial configuration on\n`z` to `cP` at time `TP`, at its exit `pexit` and not at `pexit` before, with a nonblank block of'),
    ('/-- **Through the guess and the rewind.** Let the setup `P` run from its initial configuration on\n`z` to `cP` at time `TP`, at its exit `pexit` and not at `pexit` before, with a nonblank block of',
     '/-- **No branch halts before the handoff.**'),
    ('/-- **The whole branch.** Under the setup hypotheses of `Turing.guessRunTM_runWith_handoff`,',
     '/-- **A setup that halts before its exit.**'),
    ('/-- **Through the guess and the rewind.** Let the setup `P` run from its initial configuration on\n`z` to `cP` at time `TP`, at its exit `pexit` and not at `pexit` before, with tape `j` blank',
     None),
    ('/-! The state family\'s fibers, one per phase: the reading of `Turing.GuessRunPhase.CtlState`. -/',
     '/-- **The control states of each phase of the guess-then-run host**: those of'),
    ('section GuessCtlRunPhases\n', 'end GuessCtlRunPhases\n'),
    ('section GuessCtlRunRed\n', 'end GuessCtlRunRed\n'),
]
pieces = []
for n, (a, b) in enumerate(regions, 1):
    i = s.index(a); assert s.count(a) == 1, n
    if b is None:
        j = s.rindex('\nend Turing')
    else:
        j = s.index(b, i)
        if b.startswith('end '):
            j += len(b)  # a section's own end belongs inside the seal
    pieces.append((i, j, n))
for i, j, n in sorted(pieces, reverse=True):
    s = s[:i] + block(n) + s[i:j] + endb(n) + s[j:]
open(out, 'w', encoding='utf-8').write(s)
print('sealed', len(SEAL), 'definitions in', len(pieces), 'regions; erased', len(SIMPDEFS))
