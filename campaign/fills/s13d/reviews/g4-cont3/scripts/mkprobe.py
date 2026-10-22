# usage: mkprobe.py <module file> <meta tail file> <commands file> <out file>
# Copies the module, adds `import Lean.Util.FoldConsts` after its imports, and appends the meta
# tail (outside `namespace Turing`) and the probe commands.
import sys
src, tail, cmds, out = sys.argv[1:5]
L = open(src, encoding='utf-8').read().rstrip('\n').split('\n')
last = max(i for i, l in enumerate(L) if l.startswith('import '))
L.insert(last + 1, 'import Lean.Util.FoldConsts')
assert L[-1] == 'end Turing', L[-1]
T = open(tail, encoding='utf-8').read().replace('g4c2', 'g4c3')
C = open(cmds, encoding='utf-8').read()
open(out, 'w', encoding='utf-8').write('\n'.join(L) + '\n\n' + T.rstrip('\n') + '\n\n' + C)
print('module lines', len(L), '-> probe', out)
