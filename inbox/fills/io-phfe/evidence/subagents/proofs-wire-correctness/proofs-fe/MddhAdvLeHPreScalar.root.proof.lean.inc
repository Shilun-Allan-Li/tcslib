by
    intro κ w pp ab rs t real castScalar L S U A0 v0
    letI : Fact (1 < pp.group.order) := ⟨pp.group.order_prime.one_lt⟩
    let M : Matrix (Fin (ℓ.eval κ)) (Fin 2) pp.group.G := fun i j =>
      if j = 0 then
        (pp.generator ^ (ab 0).val) ^ (L i 0).val * pp.generator ^ (L i 2).val
      else (pp.generator ^ (ab 1).val) ^ (L i 1).val * pp.generator ^ (L i 2).val
    let v : Fin (ℓ.eval κ) → pp.group.G := fun i =>
      (pp.generator ^ (ab 0 * rs 0).val) ^ (L i 0).val *
        (pp.generator ^ (ab 1 * rs 1).val) ^ (L i 1).val *
        (pp.generator ^ (if real then rs 0 + rs 1 else t).val) ^ (L i 2).val
    -- Reuse the proved scalar-left action for the entire implicit base matrix.
    have hBase : M = pp.group.expMat pp.generator (L * A0) := ?_
    swap
    · rw [← pp.group.expMat_mul_left pp.generator L A0]
      funext i j
      fin_cases j <;>
        norm_num only [Fin.mk_zero, Fin.mk_one, M, matMulGroup_apply, groupDot_eq, Fin.prod_univ_three,
          pp.group.expMat_apply, A0, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ZMod.val_zero,
          ZMod.val_one pp.group.order, pow_zero, pow_one, one_pow, mul_one, one_mul,
          ↓reduceIte]
      all_goals rfl
    -- The planted column is the already-proved exponent dot product on three coordinates.
    have hPlant : v = pp.group.expVec pp.generator (Matrix.mulVec L v0) := ?_
    swap
    · funext i
      have hDot := pp.group.groupDot_expVec pp.generator v0 (L i)
      simp only [groupDot_eq, Fin.prod_univ_three, pp.group.expVec_apply, v0,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at hDot
      rw [pp.group.expVec_apply]
      refine (show v i = pp.generator ^ (dotProduct (L i) v0).val from ?_)
      rw [dotProduct_comm]
      exact hDot
    -- Reuse the proved scalar-right action for each ordinary real response column.
    have hReal (i : Fin (ℓ.eval κ)) (j : Fin (d.eval κ)) :
        M i 0 ^ (S 0 j).val * M i 1 ^ (S 1 j).val =
          pp.group.expMat pp.generator ((L * A0) * S) i j := ?_
    swap
    · have hTransport := congrFun
        (congrFun (pp.group.expMat_mul pp.generator (L * A0) S) i) j
      simpa only [hBase, groupMatMul_apply, groupDot_eq, Fin.prod_univ_two] using hTransport
    have hResponse :
        (fun (i : Fin (ℓ.eval κ)) (j : Fin (d.eval κ)) =>
          if j.val = w.1.val then v i
          else if j.val < w.1.val then M i 0 ^ (S 0 j).val * M i 1 ^ (S 1 j).val
          else pp.generator ^ (U i j).val) =
          pp.group.expMat pp.generator (fun i j =>
            if j.val = w.1.val then Matrix.mulVec L v0 i
            else if j.val < w.1.val then ((L * A0) * S) i j else U i j) := ?_
    swap
    · funext i j
      rw [pp.group.expMat_apply]
      by_cases hSelected : j.val = w.1.val
      · simpa only [if_pos hSelected, pp.group.expVec_apply] using congrFun hPlant i
      · simp only [if_neg hSelected]
        by_cases hPrior : j.val < w.1.val
        · simpa only [if_pos hPrior, pp.group.expMat_apply] using hReal i j
        · simp only [if_neg hPrior]
    -- Read the public constructor and actual preprocessor, then assemble their data fields.
    rw [G.dlinChallenge_eq, G.mddhPreChallenge_eq p hp d ℓ κ w]
    exact congrArg₂
      (fun (N : Matrix (Fin (ℓ.eval κ)) (Fin 2) pp.group.G)
        (R : Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) pp.group.G) =>
        (⟨pp, N, R⟩ : G.MDDHChallenge d ℓ κ)) hBase hResponse
