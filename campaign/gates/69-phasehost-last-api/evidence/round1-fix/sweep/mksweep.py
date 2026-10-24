"""Copy a module with `attribute [local irreducible] Turing.phaseHostTM` after its imports (python3 -I mksweep.py <in> <out>)."""
import sys
src = open(sys.argv[1], encoding='utf-8').read().split('\n')
last = max(i for i, l in enumerate(src) if l.startswith('import '))
src.insert(last + 1, '\nattribute [local irreducible] Turing.phaseHostTM\n')
open(sys.argv[2], 'w', encoding='utf-8').write('\n'.join(src))
