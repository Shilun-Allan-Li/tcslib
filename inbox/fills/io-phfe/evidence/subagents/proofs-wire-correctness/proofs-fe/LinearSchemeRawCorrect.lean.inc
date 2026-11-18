theorem scheme_raw_correct (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ zDim κ pp) (s : EncDraw G κ pp) (t : KeyDraw G PG κ pp f) :
    let S := scheme_raw G PG zDim κ pp
    S.dec f M x (S.keyCore (S.setupCore a).2 f M t)
        (S.encCore (S.setupCore a).1 x (pp.group.expVec pp.generator z) s) =
      pp.group.pair pp.generator (leak G PG zDim κ pp f M x z) := by
  simpa only [scheme_raw_eq] using (pi_dec_eq G PG zDim κ pp f M x z a s t)
