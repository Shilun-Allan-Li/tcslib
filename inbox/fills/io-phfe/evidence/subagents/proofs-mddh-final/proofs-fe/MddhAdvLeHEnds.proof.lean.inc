by
    intro κ
    constructor
    · dsimp only [hybrid]
      simp only [accept_eq, G.mddhGame_eq d ℓ D false κ, G.mddhSample_eq d ℓ false κ,
        ProbComp.prob_bind, ProbComp.expect_bind, ProbComp.expect_pure,
        Bool.false_eq_true, if_false, Nat.not_lt_zero]
    · dsimp only [hybrid]
      simp only [accept_eq, G.mddhGame_eq d ℓ D true κ, G.mddhSample_eq d ℓ true κ,
        ProbComp.prob_bind, ProbComp.expect_bind, ProbComp.expect_pure,
        Bool.true_eq_true, if_true, Fin.is_lt]
