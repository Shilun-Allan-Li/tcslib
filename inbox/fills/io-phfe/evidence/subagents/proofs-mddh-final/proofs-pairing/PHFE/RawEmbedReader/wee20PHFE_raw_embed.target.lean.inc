/-- The raw PHFE output embedding is precisely the published class-value embedding
at every security parameter and public parameter; no efficiency or correctness premise
is needed. This projection reader preserves the parameter-dependent value/output types. -/
theorem wee20PHFE_raw_embed (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) :
    (wee20PHFE_raw G ℓ n d PG).embed = PHFE.embedValue G ℓ n d := sorry
