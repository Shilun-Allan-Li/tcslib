import itertools, random
from fractions import Fraction as F
random.seed(1)
strs=lambda m: [list(t) for t in itertools.product([False,True],repeat=m)]
def gap(M,m,x): return sum(1 for r in strs(m) if M(x,r) is True) - sum(1 for r in strs(m) if M(x,r) is False)
def randProb(m,A): return F(sum(1 for r in strs(m) if A(r)),2**m)
def rndM(seed):
    rr=random.Random(seed); tbl={}
    def M(x,r):
        k=(tuple(x),tuple(r))
        if k not in tbl: tbl[k]=rr.choice([True,False,None])
        return tbl[k]
    return M
neg=lambda M:(lambda x,r: None if M(x,r) is None else (not M(x,r)))
pad=lambda M,p:(lambda x,r: M(x,r[:p(len(x))]) if all(not b for b in r[p(len(x)):]) else None)
def summ(M1,M2):
    def f(x,r):
        if not r: return None
        return M1(x,r[1:]) if r[0] else M2(x,r[1:])
    return f
def prod(M1,M2,p):
    def f(x,r):
        a=M1(x,r[:p(len(x))]); b=M2(x,r[p(len(x)):])
        return (a==b) if (a is not None and b is not None) else None
    return f
const=lambda b:(lambda x,r: b if all(not c for c in r) else None)
def coin(M,p):
    def f(x,r):
        v=M(x,r[:p(len(x))]); rest=r[p(len(x)):]
        return v if v is not None else (rest[0] if rest else False)
    return f
ok=lambda c,s: print(('OK   ' if c else 'FAIL ')+s)
x=[True,False]; n=len(x)
M1,M2=rndM(1),rndM(2)
for m in range(0,5):
    assert gap(neg(M1),m,x)==-gap(M1,m,x)
ok(True,'gap_negVerifier')
p=lambda n:2
ok(all(gap(pad(M1,p),m,x)==gap(M1,2,x) for m in range(2,7)),'gap_padVerifier (m >= p)')
ok(all(gap(summ(M1,M2),m+1,x)==gap(M1,m,x)+gap(M2,m,x) for m in range(0,5)),'gap_sumVerifier')
ok(all(gap(prod(M1,M2,p),2+m,x)==gap(M1,2,x)*gap(M2,m,x) for m in range(0,4)),'gap_prodVerifier')
ok(all(gap(const(b),m,x)==(1 if b else -1) for b in (True,False) for m in range(0,5)),'gap_constVerifier')
B=lambda x,r: (sum(r)+len(x))%3==0
ok(all(F(gap(lambda x,r:B(x,r),m,x))==2**m*(2*randProb(m,lambda r:B(x,r))-1) for m in range(0,6)),'gap_boolVerifier')
ok(all(randProb(m,lambda r: coin(M1,p)(x,r) is True)==F(1,2)+F(gap(M1,2,x),2**3) for m in range(3,7)),'randProb_coinFill (m >= p+1)')
# polyLen padding arithmetic used in sketches
polyLen=lambda a,k,n:a*(n+1)**k
ok(all(polyLen(a1+a2,max(k1,k2),n)>=polyLen(a1,k1,n) and polyLen(a1+a2+1,max(k1,k2),n)>=polyLen(a1+a2,max(k1,k2),n)+1 for a1 in range(4) for a2 in range(4) for k1 in range(3) for k2 in range(3) for n in range(6)),'IsGapP.add schedule bounds')
ok(all(polyLen(a+1,k,n)>=polyLen(a,k,n)+1 for a in range(5) for k in range(3) for n in range(6)),'inPP_iff_exists_isGapP schedule bound')
ok(all(polyLen(2*A,K,n)==2*polyLen(A,K,n) for A in range(4) for K in range(3) for n in range(5)),'IsGapP.mul schedule')
ok(all(((0<1-2*f)==(f<=0)) for f in range(-5,6)),'InPP.compl integer step')
