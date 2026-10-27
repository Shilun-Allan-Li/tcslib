"""Seal the NDHost API PR's changed regions (python3 -I): mkseal_nf.py <NDHost.lean> <out.lean>.
Inserts, at the top of each changed region, the other-file TCSlib definitions it reaches as local
irreducible, and erases the four @[simp] TCSlib definitions of the environment."""
import sys
src, out = sys.argv[1:3]
s = open(src, encoding='utf-8').read()
SEAL = ['Turing.moveInputPos', 'Turing.Cfg.inputSymbol', 'Turing.Cfg.workTapeSymbols', 'Turing.Cfg.init',
        'Turing.Action.apply', 'Turing.Action.mapState', 'Turing.Cfg.mapState', 'Turing.NDTM.stepWith',
        'Turing.NDTM.initCfg', 'Turing.NDTM.runWith', 'Turing.MultiTapeTM.toNDTM', 'Turing.MultiTapeTM.initCfg',
        'Turing.MultiTapeTM.runFrom', 'Turing.MultiTapeTM.step', 'Turing.FinTM.bufferTape', 'Turing.skipTM',
        'Turing.skipBackTM']
SIMPDEFS = ['Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg', 'Turing.NDTM.initCfg']
block = ('\n-- seal: the other-file TCSlib definitions the changed code reaches, and the @[simp] ones erased\n'
         'attribute [-simp] ' + ' '.join(SIMPDEFS) + '\n'
         'attribute [local irreducible]\n' + ''.join('  ' + d + '\n' for d in SEAL) + '\n')
a1 = '/-- The configuration after writing the word `s`, in the writer state `q`, before testing the\n'
assert s.count(a1) == 1
s = s.replace(a1, block + a1)
a2 = '/-- **The control states of each phase of the controller-stopped guess-then-run host**'
assert s.count(a2) == 1
s = s.replace(a2, block + a2)
open(out, 'w', encoding='utf-8').write(s)
print('sealed', len(SEAL), 'definitions in 2 regions; erased', len(SIMPDEFS))
