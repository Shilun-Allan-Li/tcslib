"""Insert a tail of review commands into a copy of the module, before `end FinNDTM` (python3 -I).
usage: python3 -I append_tail.py <module.lean> <tail> <out.lean>"""
import sys
L = open(sys.argv[1], encoding='utf-8').read().split('\n')
assert L[-4] == 'end FinNDTM' and L[-2] == 'end Turing', L[-4:]
t = open(sys.argv[2], encoding='utf-8').read().split('\n')
open(sys.argv[3], 'w', encoding='utf-8').write('\n'.join(L[:-4] + t + L[-4:]))
print('wrote', sys.argv[3])
