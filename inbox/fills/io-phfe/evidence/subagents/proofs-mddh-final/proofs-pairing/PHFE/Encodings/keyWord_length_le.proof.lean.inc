/-- Every function-key word fits the garbling's uniform fixed width.

**Proof sketch.** Count the original function bits and group entries in each key block.
Apply `mCount_le_mBound` to its actual function, then the explicit `skLen_eval` reader. -/
theorem keyWord_length_le (G : BilinearGen) {ℓ n : PolyExpr} {d : ℕ}
    (PG : PartialGarbling.Raw ℓ (n.mul n) (TensorFn ℓ n d)) (κ : ℕ)
    (pp : PublicParams G κ) (sk : Key G PG κ pp) :
    (keyWord G PG κ pp sk).length ≤ (skLen G PG).eval κ := by
  have hLen :
      (keyWord G PG κ pp sk).length =
        2 * (tensorFnLen ℓ (n.mul n) G.wG d).eval κ +
          (8 * n.eval κ ^ 3 + 6 * n.eval κ ^ 2 +
            (6 * ℓ.eval κ + 8) * PG.mCount κ pp.orderParam
              (decodeFunction G ℓ n d κ pp sk.function)) * G.wG.eval κ + 10 := ?_
  swap
  · simp only [keyWord_eq, Wire.quadraticKey_eq, Wire.linearKey_eq,
      length_pairEncode, List.length_ofFn, Wire.groupMatrix_length,
      phfeClass_fnLen, Quadratic.piDim_eq, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const]
    ring
  have hNode :
      (6 * ℓ.eval κ + 8) * PG.mCount κ pp.orderParam
          (decodeFunction G ℓ n d κ pp sk.function) ≤
        (6 * ℓ.eval κ + 8) * PG.mBound.eval κ :=
    mul_le_mul_of_nonneg_left
      (PG.mCount_le_mBound κ pp.orderParam (decodeFunction G ℓ n d κ pp sk.function))
      (Nat.zero_le _)
  rw [hLen, skLen_eval]
  exact add_le_add_right
    (add_le_add_left
      (mul_le_mul_of_nonneg_right
        (add_le_add_left hNode (8 * n.eval κ ^ 3 + 6 * n.eval κ ^ 2))
        (Nat.zero_le _))
      (2 * (tensorFnLen ℓ (n.mul n) G.wG d).eval κ)) 10
