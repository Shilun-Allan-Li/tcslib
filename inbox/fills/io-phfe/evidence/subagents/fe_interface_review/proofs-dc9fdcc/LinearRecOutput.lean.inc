theorem rec_output_eq_eval (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (j : Fin (n'.eval κ)) :
    PG.recVec κ pp.orderParam f x (Sum.inl j) = PG.eval κ pp.orderParam f x j := by
  simpa only [PartialGarbling.Raw.pgb_eq, PartialGarbling.pgbCore_eq,
    Pi.zero_apply, sub_zero, Matrix.zero_vecMul, Sum.elim_single_zero,
    single_one_dotProduct] using
    (PG.reconstruct κ pp.orderParam f x (Pi.single j 1) 0)
