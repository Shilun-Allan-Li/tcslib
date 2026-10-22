# usage: mkinmodule.py <module file> <appendix file> <out file>
# Copies the module and inserts the appendix just before its final `end Turing`.
import sys
src, app, out = sys.argv[1:4]
L = open(src, encoding='utf-8').read().rstrip('\n').split('\n')
assert L[-1] == 'end Turing'
A = open(app, encoding='utf-8').read().rstrip('\n')
open(out, 'w', encoding='utf-8').write('\n'.join(L[:-1]) + '\n' + A + '\n\nend Turing\n')
print('ok', out)
