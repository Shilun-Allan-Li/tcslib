by
    intro κ j real
    letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
    let Target (pp : PublicParams G κ) : Type :=
      Matrix (Fin (ℓ.eval κ)) (Fin 3) (ZMod pp.group.order) ×
        SType κ pp × UType κ pp
    let castMatrix (pp : PublicParams G κ) (m n : ℕ) :
        Matrix (Fin m) (Fin n) (ZMod (p κ)) ≃
          Matrix (Fin m) (Fin n) (ZMod pp.group.order) :=
      Equiv.arrowCongr (Equiv.refl (Fin m))
        (Equiv.arrowCongr (Equiv.refl (Fin n))
          (ZMod.ringEquivCongr (order_eq_of_publicParams G p hp κ pp).symm).toEquiv)
    let tapeEquiv (pp : PublicParams G κ) : Tape κ ≃ Target pp :=
      Equiv.prodCongr (castMatrix pp (ℓ.eval κ) 3)
        (Equiv.prodCongr (castMatrix pp 2 (d.eval κ))
          (castMatrix pp (ℓ.eval κ) (d.eval κ)))
    let kernel (pp : PublicParams G κ) (τ : Target pp) : ℝ :=
      ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)) fun ab =>
        ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)) fun rs =>
          ProbComp.expect (ProbComp.sample (ZMod pp.group.order)) fun t =>
            obs κ j pp τ.2.1 τ.2.2 (τ.1 * A0 κ pp ab)
              (Matrix.mulVec τ.1
                ![ab 0 * rs 0, ab 1 * rs 1, if real then rs 0 + rs 1 else t])
    -- Read the actual game and its preprocessor; the only casts are the public-order ones.
    have hRead :
        avgTape κ (fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) real)) =
          avgTape κ (fun τ : Tape κ => ProbComp.expect (publicParamsGen G κ)
            (fun pp => kernel pp (tapeEquiv pp τ))) := ?_
    swap
    · dsimp only [avgTape, redGame, kernel, tapeEquiv, castMatrix]
      simp only [accept_eq, G.dlinSample_eq, ProbComp.prob_bind,
        ProbComp.expect_bind, ProbComp.expect_pure, ProbComp.prob_pure,
        G.mddhPre_eq, hPreScalar, obs, ProbComp.prob_eq_expect]
      all_goals rfl
    -- The advice law is independent of pp, so Fubini precedes the pointwise equivalence.
    rw [hRead]
    dsimp only [avgTape]
    rw [← ProbComp.expect_expect_sample (publicParamsGen G κ) (Tape κ)
      (fun pp τ => kernel pp (tapeEquiv pp τ))]
    apply congrArg (ProbComp.expect (publicParamsGen G κ))
    funext pp
    rw [ProbComp.expect_sample_equiv (tapeEquiv pp) (kernel pp)]
    -- Split the uniform product, retaining each entire matrix and every unused coordinate.
    simp only [← Bridge.expect_sample_pair, ProbComp.expect_bind, ProbComp.expect_pure]
    dsimp only [planted]
    rw [ProbComp.expect_sample_comm]
    apply congrArg (ProbComp.expect (ProbComp.sample (SType κ pp)))
    funext S
    rw [ProbComp.expect_sample_comm]
    apply congrArg (ProbComp.expect (ProbComp.sample (UType κ pp)))
    funext U
    -- Move L inside ab, rs and t using the same published independent-sample law.
    dsimp only [kernel, plantedCore]
    rw [ProbComp.expect_sample_comm]
    apply congrArg
      (ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)))
    funext ab
    rw [ProbComp.expect_sample_comm]
    apply congrArg
      (ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)))
    funext rs
    exact ProbComp.expect_sample_comm (fun L t =>
      obs κ j pp S U (L * A0 κ pp ab)
        (Matrix.mulVec L
          ![ab 0 * rs 0, ab 1 * rs 1, if real then rs 0 + rs 1 else t]))
