by
    intro c ρ
    have hLength : (List.ofFn ρ).length = D.coinLen κ :=
      (B.length_ofFn_coins κ ρ).trans
        ((congrArg (fun q : PolyExpr => q.eval κ) hB.coins_eq).trans
          (D.coinLen_eq κ).symm)
    rw [G.dlinToMddh_eq p hp d ℓ D ω κ c (List.ofFn ρ),
      D.distinguisherL_eq κ (G.mddhPre p hp d ℓ κ (ω κ) c)
        (NUPPT.coinsCongr (A := B) (B := D) hB.coins_eq κ ρ),
      NUPPT.runAt_coinsCongr (A := B) (B := D) hB.coins_eq κ
        (G.mddhPre p hp d ℓ κ (ω κ) c) ρ,
      List.take_of_length_le hLength.le]
