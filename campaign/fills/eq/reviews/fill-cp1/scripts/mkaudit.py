"""Build the axiom/audit probe: the head module with `import Lean`, the audit tail, `#print axioms`
for every declaration of the module, the constant walk of the new privates and the target, and the
sorry-source walks (python3 -I).
usage: python3 -I mkaudit.py <NTimeDiagonalizer.lean> <audit_tail.lean.txt> <out>"""
import re, sys
src, tail, out = sys.argv[1:4]
L = open(src, encoding='utf-8').read().split('\n')
assert L[15] == 'import TCSlib.Complexity.TuringMachine.BufferWords' and L[16] == '', L[15:17]
L.insert(16, 'import Lean')
assert L[-2] == 'end Turing.NTimeDiag' and L[-1] == '', L[-3:]
DECL = re.compile(r'^(?:private\s+)?(?:theorem|lemma|def|abbrev)\s+(\S+)')
names = ['Turing.NTimeDiag.' + m.group(1) for l in L if (m := DECL.match(l))]
assert len(names) == 25, names
new = [n for n in names if '.qy_' in n]; assert len(new) == 3, new
stops = [n for n in names if n not in new and n != 'Turing.NTimeDiag.exists_queryTM']
assert len(stops) == 21
tl = open(tail, encoding='utf-8').read()
assert tl.count('@STOPS@') == 1
tl = tl.replace('@STOPS@', ', '.join('`' + n for n in stops))
text = '\n'.join(L[:-1]) + '\n' + tl + '\n'
text += ''.join(f'#print axioms {n}\n' for n in names) + '\n'
text += '#eq_audit ' + ' '.join(new + ['Turing.NTimeDiag.exists_queryTM']) + '\n\n'
text += '#eq_sorry ' + ' '.join(new + ['Turing.NTimeDiag.exists_queryTM', 'Turing.NTimeDiag.exists_diagonalizer']) + '\n\n'
text += '#eq_generated\n'
open(out, 'w', encoding='utf-8').write(text)
print('wrote', out, len(text.split('\n')), 'lines;', len(names), 'prints;', new)
