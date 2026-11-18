by
      have hR : (fun i => sk.R i m) =
          pp.group.expVec pp.generator (fun i => R i m) := ?_
      swap
      · funext i
        dsimp only [sk]
        simp only [keyCore_eq, pp.group.expMat_apply, pp.group.expVec_apply]
        rfl
      rw [hR]
      dsimp only [ct]
      simp only [encCore_eq, setupCore_eq]
      rw [pp.group.expMat_mul, pp.group.expVec_vecMul, pp.group.expVec_vecMul,
        ← pp.group.expVec_add, Matrix.mul_assoc, ← Matrix.vecMul_add,
        ← Matrix.mul_add, ← Matrix.vecMul_vecMul, pp.group.pair_expVec]
      rfl
