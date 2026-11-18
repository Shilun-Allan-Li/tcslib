/-- The actual index/seed nuisance draws average to the explicit PRG advice law;
construction-specific averaging glue for [JLS26, Lemma 4.2, p. 19]. The Boolean index
retains G.idSamp's exact pushforward law; no uniformity of G.Idx is assumed.

**Proof sketch.** Read the concrete joint draws and idCore. Reindex the advice law
through its supplied record/product equivalence. Split products with the existing
expect_sample_pair identity, discard the unused repetition draw with expect_const,
and commute the remaining independent samples using expect_sample_comm. -/
theorem Params.prg_nuisance_average (P : Params) (π : PrimeSchedule) (N : ℕ) :
    let κ := P.kappaOfN N
    ∀ f : P.G.Idx (P.n κ) → (Fin (P.n κ) → Bool) →
      (Fin (P.m κ) → Fin (P.B κ)) →
      Matrix (Fin (P.n κ)) (Fin (P.ℓ κ)) (ZMod (π κ).p) →
      (Fin κ → Fin (P.n κ) → ZMod (π κ).p) → ℝ,
    ProbComp.expect (P.idSamp' κ (π κ)) (fun I =>
      ProbComp.expect (ProbComp.sample (P.Draw κ (π κ))) (fun d =>
        ProbComp.expect
          (ProbComp.sample (Fin κ → Fin (P.n κ) → ZMod (π κ).p))
          (fun u => f I.1 d.1 I.2.1 I.2.2 u))) =
      ProbComp.expect (ProbComp.sample (P.PRGAdvice π N)) (fun ω =>
        ProbComp.expect (P.G.idSamp (P.n κ)) (fun I =>
          ProbComp.expect (ProbComp.sample (Fin (P.n κ) → Bool))
            (fun σ => f I σ ω.buckets ω.matrix ω.uniform))) := by
  dsimp only
  intro f
  simp only [P.idSamp'_eq, ProbComp.expect_map, P.idCore_eq, P.G.idSamp_eq,
    ProbComp.expect_bind, ProbComp.expect_pure]
  rw [← ProbComp.expect_sample_equiv (PRGAdvice.prodEquiv P π N).symm]
  simp only [PRGAdvice.prodEquiv_eq]
  simp_rw [← Bridge.expect_sample_pair, ProbComp.expect_bind, ProbComp.expect_pure,
    ProbComp.expect_const]
  rw [ProbComp.expect_sample_comm]
  congr 1
  funext buckets
  rw [ProbComp.expect_sample_comm]
  congr 1
  funext matrix
  conv_lhs =>
    arg 2
    ext a
    rw [ProbComp.expect_sample_comm]
  rw [ProbComp.expect_sample_comm]
