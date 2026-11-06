# usage: mkseal.py SRC OUT NAMESFILE [EXCLUDE ...] : whole-file seal after the `open` line (line 82)
import sys
src,out,nf=sys.argv[1],sys.argv[2],sys.argv[3]
excl=set(sys.argv[4:])
names=[l.strip() for l in open(nf) if l.strip() and l.strip() not in excl]
L=open(src).read().split('\n')
i=next(k for k,l in enumerate(L) if l.startswith('open Complexity Turing NumberTheory Finset'))
L.insert(i+1,'-- REVIEW SEAL (fac): every foreign definition collected from the elaborated terms\nattribute [local irreducible] '+' '.join('_root_.'+n for n in names))
open(out,'w').write('\n'.join(L))
print(len(names),'names sealed; inserted after line',i+1)
