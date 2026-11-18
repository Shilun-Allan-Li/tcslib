by
    rw [accept_eq (G.dlinMatrixGame D false κ), G.dlinMatrixGame_eq D false κ,
      ProbComp.prob_bind, G.dlinMatrixSample_eq false κ, ProbComp.expect_bind]
    apply congrArg (ProbComp.expect (publicParamsGen G κ))
    funext pp
    rw [ProbComp.expect_bind]
    dsimp only [P]
    apply congrArg
      (ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)))
    funext ab
    simp only [ProbComp.expect_bind, ProbComp.expect_pure, Bool.false_eq_true, if_false]
    let word (u : Fin 3 → ZMod pp.group.order) : List Bool :=
      G.dlinEnc κ (G.dlinChallenge κ pp
        (pp.generator ^ (ab 0).val) (pp.generator ^ (ab 1).val)
        (pp.generator ^ (u 0).val) (pp.generator ^ (u 1).val)
        (pp.generator ^ (u 2).val))
    let obs (u : Fin 3 → ZMod pp.group.order) : ℝ :=
      ProbComp.prob ((ProbComp.sample (D.Coins κ)).bind fun r =>
        .pure (D.distinguisherL κ (word u) r)) (fun b => b = true)
    change ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order))
        (fun _ => ProbComp.expect (ProbComp.sample (Fin 3 → ZMod pp.group.order)) obs) =
      ProbComp.expect (ProbComp.sample (Fin 3 → ZMod pp.group.order)) (H pp ab)
    rw [ProbComp.expect_const (ProbComp.sample (Fin 2 → ZMod pp.group.order))
      (ProbComp.expect (ProbComp.sample (Fin 3 → ZMod pp.group.order)) obs)]
    apply congrArg
      (ProbComp.expect (ProbComp.sample (Fin 3 → ZMod pp.group.order)))
    funext u
    let verdict : D.Coins κ → Bool := fun r => D.distinguisherL κ (word u) r
    change ProbComp.prob
        ((ProbComp.sample (D.Coins κ)).bind fun r => .pure (verdict r))
        (fun b => b = true) =
      ProbComp.prob (ProbComp.sample (D.Coins κ)) (fun r => verdict r = true)
    rw [ProbComp.prob_eq_expect (ProbComp.sample (D.Coins κ))
      (fun r => verdict r = true), ProbComp.prob_bind]
    apply congrArg (ProbComp.expect (ProbComp.sample (D.Coins κ)))
    funext r
    exact ProbComp.prob_pure (verdict r) (fun b => b = true)
