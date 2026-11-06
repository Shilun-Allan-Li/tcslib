# E1 (Fin.appendEquiv) and E2 (local instance) on RSA.lean, in place
import sys
p=sys.argv[1]; s=open(p).read()
def rep(old,new,count=1):
    global s
    assert s.count(old)==count,(old[:60],s.count(old))
    s=s.replace(old,new)
# E1: Mathlib's `Fin.appendEquiv` instead of the private copy `rsa_appendEquiv`
rep('''/-- Splitting a coin string `Fin (a + b) → Bool` into its two segments (`Fin.append`). -/
private def rsa_appendEquiv (a b : ℕ) : (Fin a → Bool) × (Fin b → Bool) ≃ (Fin (a + b) → Bool) where
  toFun s := Fin.append s.1 s.2
  invFun f := (fun i => f (Fin.castAdd b i), fun j => f (Fin.natAdd a j))
  left_inv s := by
    obtain ⟨s1, s2⟩ := s
    ext i
    · exact Fin.append_left s1 s2 i
    · exact Fin.append_right s1 s2 i
  right_inv f := Fin.append_castAdd_natAdd

''','')
rep('''  (rsa_appendEquiv _ _).trans''','''  (Fin.appendEquiv _ _).trans''')
rep('''      ((rsa_appendEquiv _ _) s) = fun i => (rsa_appendEquiv _ _) s (Fin.cast (rsa_genCoins_len n).symm i)''',
    '''      ((Fin.appendEquiv _ _) s) = fun i => (Fin.appendEquiv _ _) s (Fin.cast (rsa_genCoins_len n).symm i)''')
rep('''with `ofFn (E (s₁, s₂)) = ofFn s₁ ++ ofFn s₂`. -/''','''with `ofFn (E (s₁, s₂)) = ofFn s₁ ++ ofFn s₂` (Mathlib's `Fin.appendEquiv`, then the length cast). -/''')
# E2: the instance stays local to the file
rep('''/-- The modulus of generated parameters is nonzero. -/
private instance rsa_neZero_N''','''/-- The modulus of generated parameters is nonzero (a local instance: it is not exported). -/
private local instance rsa_neZero_N''')
open(p,'w').write(s)
print('ok')
