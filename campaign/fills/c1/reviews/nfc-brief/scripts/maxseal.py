"""Replace each 10-definition seal of the route probe (and of the review tail) by the 223-definition
maximal seal of NFSealDefs.txt. usage: python3 -I maxseal.py <in.lean> <NFSealDefs.txt> <out.lean>"""
import sys
src, defs, out = sys.argv[1:4]
t = open(src, encoding='utf-8').read()
seal = [l.strip() for l in open(defs, encoding='utf-8') if l.strip() and not l.startswith('#')]
assert len(seal) == 223 and len(set(seal)) == 223
old = ('attribute [local irreducible] Turing.Cfg.mapState Turing.MultiTapeTM.runFrom Turing.phaseHostTM\n'
       '  Turing.skipTM Turing.skipBackTM Turing.clearTM Turing.scanTM Turing.FinTM.bufferTape\n'
       '  Turing.MultiTapeTM.step Turing.Action.apply\n')
n = t.count(old)
assert n == 2, n
new = 'attribute [local irreducible]\n' + ''.join('  ' + d + '\n' for d in seal)
t = t.replace(old, new)
open(out, 'w', encoding='utf-8').write(t)
print('replaced', n, 'seals with', len(seal), 'definitions')
