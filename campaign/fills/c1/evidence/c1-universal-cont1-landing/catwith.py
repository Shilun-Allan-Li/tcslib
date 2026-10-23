"""catwith.py <InputRewind.lean> <module or variant> <out>: the new module's text, then the file's, imports merged."""
import sys
ir, un, out = sys.argv[1:4]
def split(p):
    lines=open(p,encoding='utf-8').read().split('\n')
    return [l for l in lines if l.startswith('import ')], '\n'.join(l for l in lines if not l.startswith('import '))
i1,b1=split(ir); i2,b2=split(un)
skip='import TCSlib.Complexity.TuringMachine.Build.InputRewind'
assert i2.count(skip)==1
imps=[]
for l in i1+[l for l in i2 if l!=skip]:
    if l not in imps: imps.append(l)
open(out,'w',encoding='utf-8').write('\n'.join(imps)+'\n'+b1+'\n'+b2)
