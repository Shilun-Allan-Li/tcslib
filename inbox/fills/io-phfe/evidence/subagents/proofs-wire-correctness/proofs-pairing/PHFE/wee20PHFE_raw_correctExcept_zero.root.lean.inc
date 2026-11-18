theorem wee20PHFE_raw_correctExcept_zero (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ)
    (PG : PartialGarbling.Raw ℓ (n.mul n) (PHFE.TensorFn ℓ n d)) (hPG : PHFE.PGSound PG) :
    (wee20PHFE_raw G ℓ n d PG).CorrectExcept (fun _ => 0)  := by
  exact FEScheme.Raw.Correct.correctExcept_zero (wee20PHFE_raw G ℓ n d PG)
    (wee20PHFE_raw_correct G ℓ n d PG hPG)
