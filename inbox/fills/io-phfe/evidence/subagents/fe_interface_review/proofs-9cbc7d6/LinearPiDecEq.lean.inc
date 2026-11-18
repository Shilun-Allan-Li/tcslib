/-- Π decrypts to `e(g,[zMf(x)^T])` for every honest draw and an arbitrary source-group
matrix `M` [Wee20, §4.2, p. 10, (11)]. This is perfect correctness in the exponent.

**Proof sketch.** Substitute `decFirst_correct` and `decSecond_correct` into `dec_eq`.
Use the two reconstruction coefficient identities to cancel all `sAT` powers and identify
the remaining source-group product with `leak`. Multiplicativity of pairing gives the
claimed target-group value. This proof does not introduce scalar witnesses for `M`. -/
theorem pi_dec_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ zDim κ pp) (s : EncDraw G κ pp) (t : KeyDraw G PG κ pp f) :
    dec G PG zDim κ pp f M x
        (keyCore G PG zDim κ pp (setupCore G ℓ zDim κ pp a).2 f M t)
        (encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
          (pp.group.expVec pp.generator z) s) =
      pp.group.pair pp.generator (leak G PG zDim κ pp f M x z) := by
  classical
  let v := Matrix.vecMul (Matrix.vecMul s a.1) t.1
  let K : Matrix (PG.TIdx κ pp.orderParam f ⊕ Fin (n'.eval κ))
      (PG.MIdx κ pp.orderParam f) (ZMod pp.group.order) :=
    (show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ pp.orderParam f) *
        (show Matrix _ _ (ZMod pp.group.order) from PartialGarbling.publicTensor
          (p := pp.orderParam) (M := PG.MIdx κ pp.orderParam f) x) +
      (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ pp.orderParam f)
  let e := PG.eval κ pp.orderParam f x
  let r := fun m => PG.recVec κ pp.orderParam f x (Sum.inr m)
  let egg := pp.group.pair pp.generator pp.generator
  have hRec : K *ᵥ r = Sum.elim (fun _ => 0) e := rec_matrix_eq G PG κ pp f x
  have hMask : dotProduct (Matrix.vecMul v K) r =
      dotProduct (fun j => v (Sum.inr j)) e := ?_
  · rw [← Matrix.dotProduct_mulVec, hRec, ← Sum.elim_comp_inl_inr v,
      sumElim_dotProduct_sumElim, dotProduct_zero, zero_add]
  have hLeak : groupDot (groupVecMul z M) e = leak G PG zDim κ pp f M x z := ?_
  · rw [groupDot_eq, leak_product]
    simp only [groupVecMul_apply, groupDot_eq, ← Finset.prod_pow]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    rw [← pow_mul, ← pp.group.pow_val_mul]
  have hPair :
      (∏ j, pp.group.pair pp.generator (groupVecMul z M j) ^ (e j).val) =
        pp.group.pair pp.generator (leak G PG zDim κ pp f M x z) := ?_
  · rw [← hLeak, groupDot_eq, map_prod]
    simp only [map_pow]
  have hNeg :
      (∏ j, (egg ^ (-v (Sum.inr j)).val) ^ (e j).val) =
        (egg ^ (dotProduct (fun j => v (Sum.inr j)) e).val)⁻¹ := ?_
  · have h := pp.group.groupDot_expVecT egg
      (-(fun j : Fin (n'.eval κ) => v (Sum.inr j))) e
    rw [neg_dotProduct, pp.group.pow_val_neg_GT] at h
    simpa only [groupDot_eq, pp.group.expVecT_apply, Pi.neg_apply] using h
  rw [dec_eq, decFirst_correct, decSecond_correct, groupDot_eq,
    Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, rec_output_eq_eval G PG κ pp f x]
  change
    (∏ j, (pp.group.pair pp.generator (groupVecMul z M j) *
        egg ^ (-v (Sum.inr j)).val) ^ (e j).val) *
      groupDot (pp.group.expVecT egg (Matrix.vecMul v K)) r =
        pp.group.pair pp.generator (leak G PG zDim κ pp f M x z)
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [hPair, hNeg, pp.group.groupDot_expVecT, hMask]
  simp only [mul_assoc, inv_mul_cancel, mul_one]
