theorem signalGroup_exp (G : BilinearGen) (n1 n2 : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) (s1 s2 : Fin 2 → ZMod pp.group.order)
    (z2 : Fin (n2.eval κ) → ZMod pp.group.order)
    (y1 : Fin (n1.eval κ) → ZMod pp.group.order) :
    signalGroup G n1 n2 κ pp s1 z2 (pp.group.expVec pp.generator y1) s2 =
      pp.group.expVec pp.generator (signalScalar (p := pp.orderParam) s1 z2 y1 s2) := by
  funext i
  simp only [signalGroup_eq, signalScalar_eq, BilinearGroup.expVec_apply]
  cases hi : (signalCoord (n1.eval κ) (n2.eval κ)).symm i with
  | inl u => simp only [hi, Sum.elim_inl]
  | inr u =>
      simp only [hi, Sum.elim_inr, privateTensor_eq, Matrix.kroneckerMap_apply,
        Equiv.symm_apply_apply]
      simpa only [BilinearGroup.expVec_apply] using
        congrFun (pp.group.expVec_tensor_left pp.generator y1 s2) u
