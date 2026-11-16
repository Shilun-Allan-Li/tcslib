import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
open Matrix
#check @Matrix.vecMul_add
#check @Matrix.vecMul_smul
#check @Matrix.vecMul_vecMul
#check @Matrix.dotProduct_mulVec
#check @Matrix.vecMul_submatrix
#check @Matrix.submatrix_apply
#check @Fin.init_def
#check @Fin.sum_univ_castSucc
#check @Fin.snoc_castSucc
#check @Fin.snoc_last
#check @Matrix.transpose_apply
#check @Matrix.add_dotProduct
#check @Matrix.smul_dotProduct
#check @add_dotProduct
#check @smul_dotProduct
#check @dotProduct_mulVec
#check @Matrix.vecMul_apply
#check @Equiv.ofBijective_apply
#check @Equiv.coe_addRight
#check @ZMod.val_natCast
#check @Nat.pow_div
#check @Fintype.sum_eq_single
#check @Finset.sum_ite_eq
example (n : ℕ) (v w : Fin n → ℤ) : dotProduct v w = ∑ i, v i * w i := by exact?
example (m n : ℕ) (v : Fin m → ℤ) (M : Matrix (Fin m) (Fin n) ℤ) (j : Fin n) :
  Matrix.vecMul v M j = ∑ i, v i * M i j := by exact?
example (n : ℕ) (q : Fin (n+1) → ℤ) (i : Fin n) : Fin.init q i = q i.castSucc := by exact?
