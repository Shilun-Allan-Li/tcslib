theorem simSetupCore_singular (G : BilinearGen) (ℓ zDim : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (ω : SimSetupDraw G ℓ zDim κ pp)
    (h : ¬ IsUnit (basisMatrix G κ pp ω.1 ω.2.1).det) :
    (simSetupCore G ℓ zDim κ pp ω).2.basisInv = 0 := by
  rw [simSetupCore_eq]
  exact Matrix.nonsing_inv_apply_not_isUnit _ h
