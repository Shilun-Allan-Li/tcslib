by
    intro ab ha0 ha1
    let scale : (Fin 2 → K) ≃ (Fin 2 → K) :=
      (finTwoArrowEquiv K).trans
        ((Equiv.prodCongr (Equiv.mulLeft₀ (ab 0) ha0)
          (Equiv.mulLeft₀ (ab 1) ha1)).trans ((finTwoArrowEquiv K).symm))
    let e : ((Fin 2 → K) × K) ≃ (Fin 3 → K) :=
      (Equiv.prodCongr scale (Equiv.refl K)).trans ((Fin.succFunEquiv K 2).symm)
    have hShape (rs : Fin 2 → K) (t : K) :
        e (rs, t) = ![ab 0 * rs 0, ab 1 * rs 1, t] := ?_
    swap
    · funext i
      fin_cases i <;> rfl
    dsimp only [A, B]
    rw [← ProbComp.expect_sample_equiv e (H ab), ← Bridge.expect_sample_pair]
    simp only [ProbComp.expect_bind, ProbComp.expect_pure, hShape]
