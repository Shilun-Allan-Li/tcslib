theorem mixGroup_exp (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (A1 : Matrix (Fin 2) (Fin (n1.eval κ)) (ZMod pp.group.order))
    (A2 : Matrix (Fin 2) (Fin (n2.eval κ)) (ZMod pp.group.order)) :
    mixGroup G n1 n2 κ pp (pp.group.expMat pp.generator A1)
        (pp.group.expMat pp.generator A2) =
      pp.group.expMat pp.generator (mixScalar (p := pp.orderParam) A1 A2) := by
  funext i j
  simp only [mixGroup_eq, mixScalar_eq, BilinearGroup.expMat_apply]
  cases hi : (signalCoord (n1.eval κ) (n2.eval κ)).symm i with
  | inl u =>
      simp only [hi, Sum.elim_inl, Matrix.kroneckerMap_apply,
        BilinearGroup.expMat_apply, pp.group.pow_val_mul, pow_mul]
  | inr u =>
      simp only [hi, Sum.elim_inr, Matrix.kroneckerMap_apply,
        BilinearGroup.expMat_apply, pp.group.pow_val_mul, mul_comm, pow_mul]
