by
    classical
    rw [accept_eq (G.dlinGame D false κ), G.dlinGame_eq D false κ,
      ProbComp.prob_bind, G.dlinSample_eq false κ, ProbComp.expect_bind]
    apply congrArg (ProbComp.expect (publicParamsGen G κ))
    funext pp
    rw [ProbComp.expect_bind]
    dsimp only [Q]
    apply congrArg
      (ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)))
    funext ab
    rw [ProbComp.expect_bind]
    apply congrArg
      (ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)))
    funext rs
    rw [ProbComp.expect_bind]
    apply congrArg (ProbComp.expect (ProbComp.sample (ZMod pp.group.order)))
    funext t
    rw [ProbComp.expect_pure]
    simp only [Bool.false_eq_true, if_false]
    dsimp only [H]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    let word : List Bool :=
      G.dlinEnc κ (G.dlinChallenge κ pp
        (pp.generator ^ (ab 0).val) (pp.generator ^ (ab 1).val)
        (pp.generator ^ (ab 0 * rs 0).val) (pp.generator ^ (ab 1 * rs 1).val)
        (pp.generator ^ t.val))
    let verdict : D.Coins κ → Bool := fun r => D.distinguisherL κ word r
    change ProbComp.prob
        ((ProbComp.sample (D.Coins κ)).bind fun r => .pure (verdict r))
        (fun b => b = true) =
      ProbComp.prob (ProbComp.sample (D.Coins κ)) (fun r => verdict r = true)
    rw [ProbComp.prob_eq_expect (ProbComp.sample (D.Coins κ))
      (fun r => verdict r = true), ProbComp.prob_bind]
    apply congrArg (ProbComp.expect (ProbComp.sample (D.Coins κ)))
    funext r
    exact ProbComp.prob_pure (verdict r) (fun b => b = true)
