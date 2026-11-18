by
    have hT := pp.group.groupDot_expVec pp.generator
      (fun i => t.1 i (Sum.inr j)) (Matrix.vecMul s a.1)
    simp only [groupDot_eq, pp.group.expVec_apply] at hT
    rw [dotProduct_comm] at hT
    have hAssoc := congrFun
      (pp.group.groupVecMul_matMulGroup (Matrix.vecMul s a.1) a.2.1 M) j
    simp only [groupVecMul_apply, groupDot_eq] at hAssoc
    simp only [encCore_eq, setupCore_eq, keyCore_eq]
    rw [pp.group.expVec_vecMul, pp.group.pairVec_expVec_left]
    simp only [Matrix.hadamard_apply, pp.group.expMat_apply, groupDot_eq, mul_pow,
      Finset.prod_mul_distrib, map_mul, groupVecMul_apply]
    rw [hT, hAssoc, pp.group.pair_pow_right]
    rfl
