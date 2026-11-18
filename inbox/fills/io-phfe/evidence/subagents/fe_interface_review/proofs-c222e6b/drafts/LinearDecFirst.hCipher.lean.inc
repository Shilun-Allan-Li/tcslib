by
    simp only [encCore_eq, setupCore_eq]
    rw [pp.group.expVec_vecMul, ← pp.group.expVec_add,
      pp.group.pairVec_expVec_left]
    simp only [groupVecMul_apply, groupDot_eq, Pi.add_apply,
      pp.group.pow_val_add, Finset.prod_mul_distrib, map_mul,
      ← Matrix.vecMul_vecMul]
