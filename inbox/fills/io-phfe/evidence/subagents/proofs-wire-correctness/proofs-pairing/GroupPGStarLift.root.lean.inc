theorem groupPGStar_lift (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (mu : ZMod pp.group.order)
    (t : (PG.TIdx κ pp.orderParam f ⊕ Fin (n'.eval κ)) → ZMod pp.group.order) :
    groupPGStar G PG κ pp f x (pp.generator ^ mu.val) t =
      pp.group.expVec pp.generator (PG.pgbStar κ pp.orderParam f x mu t)  := by
  rw [groupPGStar_eq]
  funext i
  cases i with
  | inl j =>
      simp only [Sum.elim_inl, pp.group.expVec_apply, PG.pgbStar_eq,
        PartialGarbling.pgbStarCore_inl]
  | inr u =>
      simp only [Sum.elim_inr, pp.group.expVec_apply, PG.pgbStar_eq,
        PartialGarbling.pgbStarCore_inr]
      by_cases h : u = PG.m0 κ pp.orderParam f
      · simp only [if_pos h, add_zero]
        exact (pp.group.pow_val_add pp.generator _ _).symm
      · simp only [if_neg h, add_zero, mul_one]
