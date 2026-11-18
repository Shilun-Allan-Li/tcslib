theorem rec_matrix_eq (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order) :
    ((show Matrix _ _ (ZMod pp.group.order) from PG.L1 κ pp.orderParam f) *
        (show Matrix _ _ (ZMod pp.group.order) from PartialGarbling.publicTensor (p :=
          pp.orderParam) (M := PG.MIdx κ pp.orderParam f) x) +
      (show Matrix _ _ (ZMod pp.group.order) from PG.L0 κ pp.orderParam f)) *ᵥ (fun u => PG.recVec κ
        pp.orderParam f x (Sum.inr u)) =
        Sum.elim (fun _ => 0) (PG.eval κ pp.orderParam f x) := by
  funext i
  have h := PG.reconstruct κ pp.orderParam f x 0 (Pi.single i 1)
  rw [PartialGarbling.Raw.pgb_eq, PartialGarbling.pgbCore_eq,
    ← Sum.elim_comp_inl_inr (PG.recVec κ pp.orderParam f x),
    sumElim_dotProduct_sumElim, ← dotProduct_mulVec, single_one_dotProduct,
    zero_dotProduct] at h
  cases i with
  | inl a =>
      simpa only [Pi.zero_apply, Pi.single_eq_of_ne Sum.inr_ne_inl, sub_zero,
        zero_dotProduct, zero_add, Sum.elim_inl] using h
  | inr j =>
      rw [← Sum.elim_zero_single j (1 : ZMod pp.group.order)] at h
      simp only [Sum.elim_inr, Pi.zero_apply, zero_sub, ← Pi.neg_apply] at h
      rw [neg_dotProduct, single_one_dotProduct] at h
      exact (eq_of_neg_add_eq_zero h).symm.trans (rec_output_eq_eval G PG κ pp f x j)
