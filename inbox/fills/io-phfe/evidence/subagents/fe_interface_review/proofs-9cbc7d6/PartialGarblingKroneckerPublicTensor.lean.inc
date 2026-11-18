/-- A known scalar matrix can move through the public-input tensor by the identity
Kronecker block. This is the singleton-column specialization of the mixed-product
law used in [Wee20, §4.2, p.10, (10); AGW20, Appendix A, (32), p.38].

**Proof sketch.** Apply Mathlib's Matrix.mul_kronecker_mul to the identity, the
single-column x matrix, R and the identity. Read the chosen singleton column through
publicTensor_apply and the published matrix/product-index equations. The second
mixed-product specialization uses the one-dimensional identity and gives the right
side after dropping its unique singleton coordinate. Do not reprove the generic
Kronecker mixed-product law. -/
theorem kronecker_mul_publicTensor {p : ℕ+} {l : ℕ} {I J : Type}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (x : Fin l → ZMod (p : ℕ)) (R : Matrix I J (ZMod (p : ℕ))) :
    Matrix.kroneckerMap (fun a b => a * b)
        (1 : Matrix (Fin l) (Fin l) (ZMod (p : ℕ))) R *
      publicTensor (p := p) (M := J) x =
        publicTensor (p := p) (M := I) x * R := by
  let X : Matrix (Fin l) (Fin 1) (ZMod (p : ℕ)) := fun i _ => x i
  have hLeft := Matrix.mul_kronecker_mul
    (1 : Matrix (Fin l) (Fin l) (ZMod (p : ℕ))) X R
    (1 : Matrix J J (ZMod (p : ℕ)))
  have hRight := Matrix.mul_kronecker_mul X
    (1 : Matrix (Fin 1) (Fin 1) (ZMod (p : ℕ)))
    (1 : Matrix I I (ZMod (p : ℕ))) R
  simp only [Matrix.one_mul, Matrix.mul_one] at hLeft hRight
  funext iu j
  rcases iu with ⟨i, u⟩
  have h := congrFun (congrFun (hLeft.symm.trans hRight) (i, u)) (0, j)
  simpa only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_one,
    Matrix.kroneckerMap_apply, Matrix.one_apply, publicTensor_apply,
    ite_true, one_mul] using h
