/-- An all-uniform-public chain is the average of its fixed-advice PRG sections;
construction-specific semantic glue for [JLS26, Lemma 4.2, p. 19]. The equality is
of acceptance probabilities; unused queries are marginalized only in expectation.

**Proof sketch.** At an image parameter, the inverse reader identifies kappa. Read the
chain endpoint and preprocessing. Reindex the comparison vector by the explicit output
Fin equivalence, then apply prg_nuisance_average to the actual adversarial verdict test. -/
theorem Params.prg_chain_accept_average (P : Params) (π : PrimeSchedule) (A : NUPPT)
    (N : ℕ) (hN : N = P.n (P.kappaOfN N)) (b : Bool) :
    accept (P.chainGame A b (P.kappaOfN N) (P.kappaOfN N)
        (π (P.kappaOfN N))) =
      ProbComp.expect (ProbComp.sample (P.PRGAdvice π N)) (fun ω =>
        accept ((P.G.idSamp N).bind fun I =>
          (ProbComp.sample (Fin N → Bool)).bind fun σ =>
          (ProbComp.sample (Fin (P.G.outLen N) → Bool)).bind fun v =>
          (ProbComp.sample (A.Coins (P.kappaOfN N))).bind fun r =>
            pure (A.distinguisherL (P.kappaOfN N)
              (P.prgPre π N ω (I, if b then P.G.eval N I σ else v)) r))) := by
  classical
  generalize hk : P.kappaOfN N = κ at hN ⊢
  subst N
  let e : (Fin (P.m κ) → Bool) ≃ (Fin (P.G.outLen (P.n κ)) → Bool) :=
    Equiv.arrowCongr (finCongr (P.m_eq κ)) (Equiv.refl Bool)
  have hOut : ∀ v : Fin (P.G.outLen (P.n κ)) → Bool,
      e.symm v = fun j => v (P.outputIndex κ j) := ?_
  swap
  · intro v
    funext j
    rw [P.outputIndex_eq]
    rfl
  have hpub : ∀ (I : P.Idx' κ (π κ)) (d : P.Draw κ (π κ))
      (u : Fin κ → Fin (P.n κ) → ZMod (π κ).p),
      P.chainPublic κ (π κ) I d u κ = u := ?_
  swap
  · intro I d u
    funext k
    simp only [P.chainPublic_eq, k.isLt, if_true]
  have havg := P.prg_nuisance_average π (P.n κ)
  simp only [P.kappaOfN_n] at havg
  specialize havg (fun I σ buckets matrix u =>
    ProbComp.expect (ProbComp.sample (Fin (P.G.outLen (P.n κ)) → Bool)) (fun v =>
      ProbComp.expect (ProbComp.sample (A.Coins κ)) (fun r =>
        if A.distinguisherL κ
          (P.challengeStr κ (π κ) (I, buckets, matrix)
            (P.publicSeed κ (π κ) u false)
            (if b then fun j => P.G.eval (P.n κ) I σ (P.outputIndex κ j)
              else fun j => v (P.outputIndex κ j))) r = true then 1 else 0)))
  simp only [accept_eq, P.chainGame_eq, ProbComp.prob_bind, ProbComp.prob_pure,
    P.prgPre_eq, P.kappaOfN_n, dif_pos rfl, hpub]
  conv_lhs =>
    arg 2
    ext I
    arg 2
    ext d
    arg 2
    ext u
    rw [← ProbComp.expect_sample_equiv e.symm]
  simp only [hOut]
  cases b <;> simpa using havg
