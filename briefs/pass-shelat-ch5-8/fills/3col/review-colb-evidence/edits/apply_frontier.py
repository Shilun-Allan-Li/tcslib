# apply_frontier.py <worktree> stubs|edit
import sys,os
R,what=sys.argv[1],sys.argv[2]; D=os.path.join(R,'TCSlib/Cryptography/ZeroKnowledge/ThreeColoring')
def rep(path,old,new):
    s=open(path).read(); assert s.count(old)==1,(path,old[:50]); open(path,'w').write(s.replace(old,new))
if what=='stubs':
    rep(D+'/Language.lean',"def edgeIdxOfMsg (m : ℕ) (w : List Bool) : ℕ := w.length % m\n",
        "def edgeIdxOfMsg (m : ℕ) (w : List Bool) : ℕ := w.length % m\n\n"
        "/-- REVIEW STUB (scratch only) of #210's next-round lemma: the defining equation of\n"
        "`edgeIdxOfMsg`. -/\n"
        "theorem edgeIdxOfMsg_eq (m : ℕ) (w : List Bool) : edgeIdxOfMsg m w = w.length % m := rfl\n")
    rep(D+'/Protocol.lean',"def msgAt (w : List Bool) (i : ℕ) : List Bool := pairFstD (pairSndD^[i] w)\n",
        "def msgAt (w : List Bool) (i : ℕ) : List Bool := pairFstD (pairSndD^[i] w)\n\n"
        "/-- REVIEW STUB (scratch only) of #210's next-round lemma: the defining equation of\n"
        "`msgAt`. -/\n"
        "theorem msgAt_eq (w : List Bool) (i : ℕ) : msgAt w i = pairFstD (pairSndD^[i] w) := rfl\n")
else:
    rep(D+'/Simulator.lean',"theorem col_zk {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) :\n"
        "    ZK (colProtocol Com ℓ) R3COL := by\n  sorry\n",
        "theorem col_zk {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) :\n"
        "    ZK (colProtocol Com ℓ) R3COL :=\n  colZK_zk_of_eqs msgAt_eq edgeIdxOfMsg_eq hC\n")
print('ok',what)
