/-- The public key has its exact polynomial wire width.

**Proof sketch.** Read the group-vector, matrix and public-key word equations. Use
`length_pairEncode` and `List.length_ofFn` for each matrix row, then evaluate `mpkLen`.
No padding is included in this count. -/
theorem quadraticMPK_length (G : BilinearGen) (ℓ n : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (pk : Quadratic.MPK G ℓ n n κ pp) :
    (Wire.quadraticMPK pp pk).length = (mpkLen G ℓ n).eval κ := by
  simp only [Wire.quadraticMPK_eq, Wire.linearMPK_eq, length_pairEncode,
    Wire.groupMatrix_length, mpkLen_eval, Quadratic.piDim_eq,
    PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  ring
