/-- The master secret has its exact polynomial wire width.

**Proof sketch.** Count the public matrix entries and the three scalar matrix blocks using
shared modular encoding length readers. Expand only the published wire equations and the
numeric width reader; collect polynomial terms. -/
theorem quadraticMSK_length (G : BilinearGen) (ℓ n : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (sk : Quadratic.MSK G ℓ n n κ pp) :
    (Wire.quadraticMSK pp sk).length = (mskLen G ℓ n).eval κ := by
  simp only [Wire.quadraticMSK_eq, Wire.linearMSK_eq, length_pairEncode,
    Wire.groupMatrix_length, Encoding.Modular.encodeMatrix_length, mskLen_eval,
    Quadratic.piDim_eq, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  ring
