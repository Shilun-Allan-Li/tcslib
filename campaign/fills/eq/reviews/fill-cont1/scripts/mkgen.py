"""Probe listing the module's non-private local constants (compiler auxiliaries included): the file
with `import Lean` after its last import, then the audit tail's `#eq_generated` (python3 -I).
usage: python3 -I mkgen.py <module.lean> <audit_tail.lean.txt> <out>"""
import sys
src, tail, out = sys.argv[1:4]
L = open(src, encoding='utf-8').read().split('\n')
last = max(i for i, l in enumerate(L) if l.startswith('import '))
L.insert(last + 1, 'import Lean')
t = open(tail, encoding='utf-8').read().replace('@STOPS@', '')
open(out, 'w', encoding='utf-8').write('\n'.join(L) + '\n' + t + '\n#eq_generated\n')
print('wrote', out)
