import itertools, numpy as np
s2=np.sqrt(2)
def regs(n): return list(itertools.product([0,1],repeat=n))
def mat(n,f): R=regs(n); return np.array([[f(y,x) for x in R] for y in R],dtype=complex)
def perm(n,sig): return mat(n,lambda y,x: 1.0 if y==sig(x) else 0.0)
def upd(x,i,v): x=list(x); x[i]=v%2; return tuple(x)
H=mat(1,lambda y,x:(1/s2)*(-1)**((x[0]*y[0])%2))
X=perm(1,lambda x:upd(x,0,x[0]+1))
Z=np.diag([(-1)**x[0] for x in regs(1)]).astype(complex)
S=np.diag([1j**x[0] for x in regs(1)])
CNOT=perm(2,lambda x:upd(x,1,x[1]+x[0]))
TOF=perm(3,lambda x:upd(x,2,x[2]+x[0]*x[1]))
I1=np.eye(2)
def applyOn(w,U,n):
    k=len(w); Rk=regs(k)
    def f(y,x):
        if all(y[i]==x[i] for i in range(n) if i not in w):
            return U[Rk.index(tuple(y[j] for j in w)),Rk.index(tuple(x[j] for j in w))]
        return 0
    return mat(n,f)
ok=lambda c,msg: print(('OK   ' if c else 'FAIL ')+msg)
ok(np.allclose(H@H,I1),'H*H=1'); ok(np.allclose(S@S,Z),'S*S=Z'); ok(np.allclose(H@Z@H,X),'HZH=X')
ok(np.allclose(X,H@S@S@H),'X=HSSH')
# applyOn algebra on random unitaries, wires (2,0) in 3
rng=np.random.default_rng(0)
def ru(d): q,_=np.linalg.qr(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d))); return q
U,V=ru(4),ru(4); w=(2,0)
ok(np.allclose(applyOn(w,U@V,3),applyOn(w,U,3)@applyOn(w,V,3)),'applyOn_mul')
ok(np.allclose(applyOn(w,U,3).conj().T,applyOn(w,U.conj().T,3)),'applyOn_conjTranspose')
ok(np.allclose(applyOn(w,np.eye(4),3),np.eye(8)),'applyOn_one')
A,B=ru(2),ru(4)
ok(np.allclose(applyOn((1,),A,3)@applyOn((2,0),B,3),applyOn((2,0),B,3)@applyOn((1,),A,3)),'commute_of_disjoint')
# kronecker bridge: castAdd wires (0..k-1) in k+m; regAppend (a,b)-> a on first k, b on last m: index order a-major
k,m=2,1; Uk=ru(4)
ok(np.allclose(applyOn((0,1),Uk,3),np.kron(Uk,np.eye(2))),'castAdd = kron(U,I) (a-major order)')
ok(np.allclose(applyOn((0,),X,1),X),'applyOn_refl (k=n=1)')
# X on wire i flips wire i
R3=regs(3)
def e(n,x): v=np.zeros(2**n,dtype=complex); v[regs(n).index(tuple(x))]=1; return v
ok(all(np.allclose(applyOn((1,),X,3)@e(3,x), e(3,upd(x,1,x[1]+1))) for x in R3),'X on wire 1 flips wire 1')
# Toffoli control one
R2=regs(2)
ok(all(np.isclose(TOF[R3.index(y),R3.index(x)], CNOT[R2.index(y[1:]),R2.index(x[1:])]) for y in R3 for x in R3 if y[0]==1 and x[0]==1),'Toffoli_apply_of_control_one')
# teleportation
bell=np.array([1/s2 if x[0]==x[1] else 0 for x in R2],dtype=complex)
allok=True; probok=True; corrok=True
for _ in range(5):
    psi=ru(2)[:,0]
    init=np.array([psi[y[0]]*bell[R2.index((y[1],y[2]))] for y in R3])
    st=applyOn((0,),H,3)@(applyOn((0,1),CNOT,3)@init)
    for y in R3:
        M=np.linalg.matrix_power(X,y[1])@np.linalg.matrix_power(Z,y[0])
        allok &= np.isclose(st[R3.index(y)],0.5*(M@psi)[y[2]])
    for m0,m1 in R2:
        p=sum(abs(st[R3.index(y)])**2 for y in R3 if y[0]==m0 and y[1]==m1); probok&=np.isclose(p,0.25)
        bob=np.array([st[R3.index((m0,m1,b))] for b in (0,1)])
        C=np.linalg.matrix_power(Z,m0)@np.linalg.matrix_power(X,m1)
        corrok&=np.allclose(C@bob,0.5*psi)
ok(allok,'teleportState_vec'); ok(probok,'teleport_outcome_prob'); ok(corrok,'teleport_correct')
sd=True
for b0,b1 in R2:
    enc=np.linalg.matrix_power(X,b1)@np.linalg.matrix_power(Z,b0)
    st=applyOn((0,),H,2)@(CNOT@(applyOn((0,),enc,2)@bell))
    sd&=np.isclose(abs(st[R2.index((b0,b1))])**2,1)
ok(sd,'superdense_decode')
