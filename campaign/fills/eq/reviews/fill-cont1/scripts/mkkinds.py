"""Build the kinds probe: the audit probe's module and tail, then the kinds command, then
`#eq_kinds` over the identifiers inside the module's namespace (python3 -I).
usage: python3 -I mkkinds.py <module.lean> <audit2_tail> <kinds2_tail> <ids file> <out>"""
import sys
src, t1, t2, idsf, out = sys.argv[1:6]
L = open(src, encoding='utf-8').read().split('\n')
last = max(i for i, l in enumerate(L) if l.startswith('import '))
L.insert(last + 1, 'import Lean')
ids = [l.strip() for l in open(idsf, encoding='utf-8') if l.strip()]
ids = [i.lstrip('←').strip() for i in ids]
text = '\n'.join(L) + '\n' + open(t1, encoding='utf-8').read() + '\n' + open(t2, encoding='utf-8').read()
text += '\nnamespace Turing.NTimeDiag\n\n'
for k in range(0, len(ids), 40):
    text += '#eq_kinds ' + ' '.join(ids[k:k + 40]) + '\n'
text += '\nend Turing.NTimeDiag\n'
open(out, 'w', encoding='utf-8').write(text)
print('wrote', out, len(ids), 'identifiers')
