theorem quadraticCT_length (G : BilinearGen) (n : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (ct : Quadratic.CT G n n κ pp) :
    (Wire.quadraticCT pp ct).length = (ctLen G n).eval κ  := by
  simp only [Wire.quadraticCT_eq, Wire.linearCT_eq, List.length_append,
    Wire.groupVector_length, ctLen_eval, Quadratic.piDim_eq, PolyExpr.eval_add,
    PolyExpr.eval_mul, PolyExpr.eval_const]
  ring
