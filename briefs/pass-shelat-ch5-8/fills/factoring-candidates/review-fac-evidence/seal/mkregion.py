# usage: mkregion.py SRC OUT NAMESFILE [EXCLUDE ...]
# Wrap every fill declaration (new `fac_*` and the 10 targets, docstring included) in
# `section revSeal / attribute [local irreducible] <names> / end revSeal`; adjacent ones merged.
import re,sys
src,out,nf=sys.argv[1],sys.argv[2],sys.argv[3]
excl=set(sys.argv[4:])
names=[l.strip() for l in open(nf) if l.strip() and l.strip() not in excl]
T={"fmult_easy","fmult_weakOneWay","exists_plantFactorer","fmult_prod_strongOneWay",
   "polyTimeComputable_samplePrimeL","statClose_samplePrimeL_pair","polyTimeComputable_samplePairRaw",
   "factoringCollection_sampleClose","factoringCollection_invProbAt_le","factoringCollection_oneWay"}
KW=r'(?:private |protected |noncomputable |@\[[^\]]*\]\s*)*(?:theorem|lemma|def|abbrev|structure|instance)\s+([^\s(:{\[]+)'
L=open(src).read().split('\n')
starts=[]
for i,l in enumerate(L):
    m=re.match(KW,l)
    if m:
        d=i
        if i>0 and L[i-1].rstrip().endswith('-/'):
            j=i-1
            while not L[j].lstrip().startswith('/--'): j-=1
            d=j
        starts.append((d,i,m.group(1)))
endfile=max(i for i,l in enumerate(L) if l.startswith('end TCSlib.Cryptography.Candidates'))
regs=[]
for k,(d,i,n) in enumerate(starts):
    e=(starts[k+1][0] if k+1<len(starts) else endfile)
    # do not swallow section headers / blank lines at the tail
    while e-1>i and (L[e-1].strip()=='' or L[e-1].lstrip().startswith('/-!')): e-=1
    if n.startswith('fac_') or n in T:
        if regs and regs[-1][1]>=d-2 and all(L[x].strip()=='' for x in range(regs[-1][1],d)): regs[-1][1]=e
        else: regs.append([d,e])
att='attribute [local irreducible] '+' '.join('_root_.'+x for x in names)
res=[]
S={a for a,b in regs}; E={b for a,b in regs}
for i,l in enumerate(L):
    if i in E: res.append('end revSeal')
    if i in S: res+=['section revSeal',att]
    res.append(l)
open(out,'w').write('\n'.join(res))
print(len(names),'names;',len(regs),'regions:',[(a+1,b) for a,b in regs])
