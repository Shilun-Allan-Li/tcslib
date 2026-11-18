by
      have hColumn :
          (fun i => pp.group.expMat pp.generator ((T * L1m + U * H) * X) i m *
            pp.group.expMat pp.generator (T * L0m + V * R) i m) =
          pp.group.expVec pp.generator
            (fun i => (T * (L1m * X + L0m) + (U * X2 + V) * R) i m) := ?_
      swap
      · funext i
        rw [pp.group.expMat_apply, pp.group.expMat_apply, pp.group.expVec_apply,
          ← pp.group.pow_val_add]
        exact congrArg (fun c : ZMod pp.group.order => pp.generator ^ c.val)
          (congrFun (congrFun hMatrix i) m)
      dsimp only [ct, K, sk]
      simp only [encCore_eq, setupCore_eq, keyCore_eq]
      rw [pp.group.expVec_vecMul, pp.group.expMat_mul, hColumn,
        pp.group.pair_expVec]
      change pp.group.pair pp.generator pp.generator ^
        (Matrix.vecMul sa (T * (L1m * X + L0m) + (U * X2 + V) * R) m).val = _
      rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
      change pp.group.pair pp.generator pp.generator ^ (value m + mask m).val = _
      exact pp.group.pow_val_add_GT _ _ _
