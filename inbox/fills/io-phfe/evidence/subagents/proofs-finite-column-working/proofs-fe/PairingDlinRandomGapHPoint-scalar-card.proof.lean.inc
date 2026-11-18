by
    letI : Fact pp.group.order.Prime := ⟨pp.group.order_prime⟩
    letI : NeZero pp.group.order := ⟨pp.group.order_prime.ne_zero⟩
    let obs (ab : Fin 2 → ZMod pp.group.order) (u : Fin 3 → ZMod pp.group.order)
        (r : D.Coins κ) : Prop :=
      D.distinguisherL κ
        (G.dlinEnc κ (G.dlinChallenge κ pp
          (pp.generator ^ (ab 0).val) (pp.generator ^ (ab 1).val)
          (pp.generator ^ (u 0).val) (pp.generator ^ (u 1).val)
          (pp.generator ^ (u 2).val))) r = true
    have h0 (ab : Fin 2 → ZMod pp.group.order) (u : Fin 3 → ZMod pp.group.order) :
        0 ≤ H pp ab u :=
      ProbComp.prob_nonneg (ProbComp.sample (D.Coins κ)) (obs ab u)
    have h1 (ab : Fin 2 → ZMod pp.group.order) (u : Fin 3 → ZMod pp.group.order) :
        H pp ab u ≤ 1 :=
      ProbComp.prob_le_one (ProbComp.sample (D.Coins κ)) (obs ab u)
    have h := dlinDiagonal_random_gap_le (K := ZMod pp.group.order) (H pp) h0 h1
    have hc := congrArg (fun n : ℕ => 2 / (n : ℝ) - 1 / (n : ℝ) ^ 2)
      (ZMod.card pp.group.order)
    exact h.trans hc.le
