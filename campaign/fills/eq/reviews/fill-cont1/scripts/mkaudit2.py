"""Build the review's audit probe: the module with `import Lean` after its last import, the audit
tail, `#print axioms` for the target and a sample of privates, then the audit commands
(python3 -I).
usage: python3 -I mkaudit2.py <module.lean> <audit2_tail.lean.txt> <out> [sample names...]"""
import sys
src, tail, out = sys.argv[1:4]
sample = sys.argv[4:]
L = open(src, encoding='utf-8').read().split('\n')
last = max(i for i, l in enumerate(L) if l.startswith('import '))
L.insert(last + 1, 'import Lean')
assert L[-2] == 'end Turing.NTimeDiag' and L[-1] == '', L[-3:]
t = open(tail, encoding='utf-8').read()
text = '\n'.join(L[:-1]) + '\n' + t + '\n'
text += '#print axioms Turing.NTimeDiag.exists_queryTM\n#print axioms Turing.NTimeDiag.exists_diagonalizer\n'
text += ''.join(f'#print axioms Turing.NTimeDiag.{n}\n' for n in sample) + '\n'
text += '#eq_locals\n\n#eq_axioms_all\n\n#eq_walk\n\n#eq_alldefs\n'
open(out, 'w', encoding='utf-8').write(text)
print('wrote', out, len(text.split('\n')), 'lines; samples', len(sample))
