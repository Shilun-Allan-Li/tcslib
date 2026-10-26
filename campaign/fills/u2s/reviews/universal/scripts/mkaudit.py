"""Build the axiom/audit probe: the head module + `import Lean`, SelfUniversal's body inlined, the
audit tail, and the prints. Usage: mkaudit.py <UniversalK.lean> <SelfUniversal.lean> <tail.lean> <decls.txt> <out>"""
import sys
uk, su, tail, decls, out = sys.argv[1:6]
U = open(uk, encoding='utf-8').read().split('\n')
assert U[11] == 'import TCSlib.Complexity.TuringMachine.Build.Rewind', U[11]
assert U[12] == '', U[12]
U.insert(12, 'import Lean')
assert U[-2] == 'end Turing' and U[-1] == '', U[-3:]
Sv = open(su, encoding='utf-8').read().split('\n')
a = Sv.index('namespace Turing'); b = len(Sv) - 1 - Sv[::-1].index('end Turing')
assert a < b and Sv.count('namespace Turing') == 1, (a, b)
body = Sv[a:b + 1]
names = [l.split()[2] for l in open(decls, encoding='utf-8').read().split('\n') if l.strip()]
assert len(names) == 79
new = [n for n in names if n.startswith('Turing.uk_')]
assert len(new) == 28
targets = ['Turing.exists_selfUniversalK', 'Turing.universalK']
prints = [f'#print axioms {n}' for n in names + ['Turing.exists_selfStartupTM', 'Turing.exists_selfUniversal']]
text = '\n'.join(U[:-1]) + '\n\n-- SelfUniversal.lean lines 66-161, inlined so that its proofs see this module\n' + '\n'.join(body) + '\n' + open(tail, encoding='utf-8').read() + '\n' + '\n'.join(prints) + '\n\n'
text += '#uk_audit ' + ' '.join(new + targets) + '\n\n'
text += '#uk_sorry ' + ' '.join(targets + ['Turing.exists_selfUniversal', 'Turing.exists_selfStartupTM', 'Turing.exists_selfStartupTMK']) + '\n\n'
text += '#uk_generated\n'
open(out, 'w', encoding='utf-8').write(text)
print('wrote', out, len(text.split('\n')), 'lines;', len(prints), 'prints')
