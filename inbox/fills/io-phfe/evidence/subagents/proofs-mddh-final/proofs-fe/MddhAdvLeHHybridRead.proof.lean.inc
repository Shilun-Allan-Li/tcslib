by
      dsimp only [hybrid]
      simp only [accept_eq, ProbComp.prob_bind, ProbComp.expect_bind,
        ProbComp.expect_pure, ProbComp.prob_pure]
      apply congrArg (ProbComp.expect (publicParamsGen G κ)); funext pp
      apply congrArg (ProbComp.expect
        (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order))))
      funext M
      apply congrArg (ProbComp.expect (ProbComp.sample (SType κ pp))); funext S
      apply congrArg (ProbComp.expect (ProbComp.sample (UType κ pp))); funext U
      dsimp only [obs]
      rw [ProbComp.prob_eq_expect]
      apply congrArg (ProbComp.expect (ProbComp.sample (D.Coins κ))); funext r
      apply congrArg (fun R :
          Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order) =>
        if D.distinguisherL κ (G.mddhEnc d ℓ κ
          ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator R⟩) r = true
        then (1 : ℝ) else 0)
      funext a b
      cases real with
      | false =>
        simp only [Bool.false_eq_true, if_false, Nat.add_zero]
        by_cases h : b.val = j.val
        · have hb : b = j := Fin.ext h
          subst b
          simp only [if_pos rfl, Nat.lt_irrefl, if_false]
        · simp only [if_neg h]
      | true =>
        simp only [↓reduceIte]
        by_cases h : b.val = j.val
        · have hb : b = j := Fin.ext h
          subst b
          simp only [Nat.lt_succ_self, if_true, if_pos rfl]
          exact Matrix.mul_apply'
        · have hCompare : b.val < j.val + 1 ↔ b.val < j.val := ?_
          swap
          · omega
          simp only [if_neg h, hCompare]
