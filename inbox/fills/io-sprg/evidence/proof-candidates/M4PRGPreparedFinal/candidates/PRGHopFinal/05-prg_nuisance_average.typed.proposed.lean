/-- The actual index/seed nuisance draws average to the explicit PRG advice law;
construction-specific averaging glue for [JLS26, Lemma 4.2, p. 19]. The Boolean index
retains G.idSamp's exact pushforward law; no uniformity of G.Idx is assumed.

**Proof sketch.** Read the concrete joint draws and idCore. Reindex the advice law
through its supplied record/product equivalence. Split the specified actual
products with expect_sample_pair, reindex their factors by an explicit proof-local
permutation with expect_sample_equiv, and discard only the unused repetition draw
with expect_const. -/
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
  let κ := P.kappaOfN N
  let pp := π κ
  let GDraw := P.G.IdDraw (P.n κ)
  let Buck := Fin (P.m κ) → Fin (P.B κ)
  let Mat := Matrix (Fin (P.n κ)) (Fin (P.ℓ κ)) (ZMod pp.p)
  let Seed := Fin (P.n κ) → Bool
  let Rep := Fin κ → (Fin (P.ℓ κ) → ZMod pp.p) ×
    (Fin (P.n κ) → Fin (P.W κ) × ZMod pp.p)
  let U := Fin κ → Fin (P.n κ) → ZMod pp.p
  let Raw := (GDraw × (Buck × Mat)) × ((Seed × Rep) × U)
  let Nuisance := Buck × (Mat × U)
  let Target := Nuisance × (GDraw × (Seed × Rep))
  let rawTest : Raw → ℝ := fun z =>
    f (P.G.idCore (P.n κ) z.1.1) z.2.1.1 z.1.2.1 z.1.2.2 z.2.2
  let targetTest : Target → ℝ := fun z =>
    f (P.G.idCore (P.n κ) z.2.1) z.2.2.1 z.1.1 z.1.2.1 z.1.2.2
  let avg : Nuisance → ℝ := fun ν =>
    ProbComp.expect (ProbComp.sample GDraw) (fun g =>
      ProbComp.expect (ProbComp.sample Seed) (fun σ =>
        f (P.G.idCore (P.n κ) g) σ ν.1 ν.2.1 ν.2.2))
  let left : ℝ := ProbComp.expect (P.idSamp' κ pp) (fun I =>
    ProbComp.expect (ProbComp.sample (P.Draw κ pp)) (fun d =>
      ProbComp.expect (ProbComp.sample U) (fun u => f I.1 d.1 I.2.1 I.2.2 u)))
  let right : ℝ := ProbComp.expect (ProbComp.sample (P.PRGAdvice π N)) (fun ω =>
    ProbComp.expect (P.G.idSamp (P.n κ)) (fun I =>
      ProbComp.expect (ProbComp.sample Seed) (fun σ =>
        f I σ ω.buckets ω.matrix ω.uniform)))
  change left = right
  have hleft : left = ProbComp.expect (ProbComp.sample Raw) rawTest := ?_
  swap
  · dsimp only [left]
    rw [P.idSamp'_eq, ProbComp.expect_map]
    simp only [P.idCore_eq]
    rw [← Bridge.expect_sample_pair (α := GDraw × (Buck × Mat))
      (β := (Seed × Rep) × U) rawTest]
    simp only [ProbComp.expect_bind, ProbComp.expect_pure, rawTest]
    apply congrArg (ProbComp.expect (ProbComp.sample (GDraw × (Buck × Mat))))
    funext a
    rw [← Bridge.expect_sample_pair (α := Seed × Rep) (β := U)
      (fun z : (Seed × Rep) × U =>
        f (P.G.idCore (P.n κ) a.1) z.1.1 a.2.1 a.2.2 z.2)]
    simp only [ProbComp.expect_bind, ProbComp.expect_pure]
  let e : Raw ≃ Target :=
    { toFun := fun z => ((z.1.2.1, z.1.2.2, z.2.2), (z.1.1, z.2.1))
      invFun := fun z => ((z.2.1, z.1.1, z.1.2.1), (z.2.2, z.1.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hperm : ProbComp.expect (ProbComp.sample Raw) rawTest =
      ProbComp.expect (ProbComp.sample Target) targetTest :=
    ProbComp.expect_sample_equiv e targetTest
  have htarget : ProbComp.expect (ProbComp.sample Target) targetTest =
      ProbComp.expect (ProbComp.sample Nuisance) avg := ?_
  swap
  · rw [← Bridge.expect_sample_pair (α := Nuisance) (β := GDraw × (Seed × Rep))
      targetTest]
    simp only [ProbComp.expect_bind, ProbComp.expect_pure, targetTest]
    apply congrArg (ProbComp.expect (ProbComp.sample Nuisance))
    funext ν
    rw [← Bridge.expect_sample_pair (α := GDraw) (β := Seed × Rep)
      (fun z : GDraw × (Seed × Rep) =>
        f (P.G.idCore (P.n κ) z.1) z.2.1 ν.1 ν.2.1 ν.2.2)]
    simp only [ProbComp.expect_bind, ProbComp.expect_pure]
    apply congrArg (ProbComp.expect (ProbComp.sample GDraw))
    funext g
    rw [← Bridge.expect_sample_pair (α := Seed) (β := Rep)
      (fun z : Seed × Rep => f (P.G.idCore (P.n κ) g) z.1 ν.1 ν.2.1 ν.2.2)]
    simp only [ProbComp.expect_bind, ProbComp.expect_pure, ProbComp.expect_const, avg]
  have hright : right = ProbComp.expect (ProbComp.sample Nuisance) avg := ?_
  swap
  · dsimp only [right]
    rw [← ProbComp.expect_sample_equiv (PRGAdvice.prodEquiv P π N) avg]
    simp only [P.G.idSamp_eq, ProbComp.expect_bind, ProbComp.expect_pure,
      PRGAdvice.prodEquiv_eq, avg]
  exact hleft.trans (hperm.trans (htarget.trans hright.symm))
