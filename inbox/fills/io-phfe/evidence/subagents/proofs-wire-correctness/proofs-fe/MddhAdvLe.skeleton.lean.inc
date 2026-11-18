/-- For every MDDH distinguisher, one advice family makes the column-hybrid bound hold for
EVERY machine realising the reduction, simultaneously at all parameters
[Wee20, §2.1, p. 4, polynomial-loss implementation of its cited implication].
The shared realisation predicate constrains only encoded challenges and coin strings of
the stated layout length, which suffices for this bound.

**Proof sketch.** For a nonzero column count, select an adjacent response-column hybrid by
the shared hybrid-gap lemma. Fix the left randomizer and other columns' masks by averaging.
For the real challenge, condition on rank two of `A₀`; for the random challenge, condition
on `det(A₀|c)=ab(t-r-s)` being nonzero. Left multiplication by the corresponding full-rank
matrix is a uniform linear map, giving the required adjacent laws. Bound their exceptional
probabilities by `p⁻²` and `3/p-3/p²+1/p³`. Transfer the typed reduction's verdict through
`RealizesOn.distinguisherL_eq`. Multiply by the column count. For zero columns the advantage
is zero, and the sentinel advice supplies the required inhabited value. -/
theorem mddhAdv_le (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ)
    (d ℓ : PolyExpr) (D : NUPPT) :
    ∃ ω : ∀ κ, MddhAdvice p d ℓ κ, ∀ B : NUPPT,
      B.RealizesOn G.dlinEnc D.coins (G.dlinToMddh p hp d ℓ D ω) →
      ∀ κ, G.mddhAdv d ℓ D κ ≤
        (d.eval κ : ℝ) * G.dlinAdv B κ + mddhSlack p d κ := by
  -- The column index is fixed by the hybrid lemma; only its three scalar tapes are averaged.
  let Tape (κ : ℕ) : Type :=
    Matrix (Fin (ℓ.eval κ)) (Fin 3) (ZMod (p κ)) ×
      Matrix (Fin 2) (Fin (d.eval κ)) (ZMod (p κ)) ×
      Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod (p κ))
  let avgTape (κ : ℕ) (f : Tape κ → ℝ) : ℝ :=
    letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
    ProbComp.expect (ProbComp.sample (Tape κ)) f
  -- These are the actual column hybrids, sharing the real base and the original D coins.
  let hybrid (κ i : ℕ) : ProbComp Bool :=
    (publicParamsGen G κ).bind fun pp =>
    (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order))).bind fun M =>
    (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order))).bind fun S =>
    (ProbComp.sample
      (Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order))).bind fun U =>
    (ProbComp.sample (D.Coins κ)).bind fun r =>
      .pure (D.distinguisherL κ (G.mddhEnc d ℓ κ
        ⟨pp, pp.group.expMat pp.generator M,
          pp.group.expMat pp.generator
            (fun a b => if b.val < i then (M * S) a b else U a b)⟩) r)
  -- The reduction experiment uses the published preprocessor and never constructs a machine.
  let redGame (κ : ℕ) (w : MddhAdvice p d ℓ κ) (real : Bool) : ProbComp Bool :=
    (G.dlinSample real κ).bind fun c =>
    (ProbComp.sample (D.Coins κ)).bind fun r =>
      .pure (D.distinguisherL κ (G.mddhPre p hp d ℓ κ w c) r)
  let redGap (κ : ℕ) (w : MddhAdvice p d ℓ κ) : ℝ :=
    advantage (redGame κ w false) (redGame κ w true)
  have hEnds : ∀ κ,
      accept (hybrid κ 0) = accept (G.mddhGame d ℓ D false κ) ∧
        accept (hybrid κ (d.eval κ)) = accept (G.mddhGame d ℓ D true κ) := sorry
  have hEndpointGap (κ : ℕ) :
      G.mddhAdv d ℓ D κ = advantage (hybrid κ 0) (hybrid κ (d.eval κ)) := ?_
  swap
  · rw [G.mddhAdv_eq d ℓ D κ, advantage_eq, advantage_eq, (hEnds κ).1, (hEnds κ).2]
  -- Known scalar DLIN draws give exactly the group-arithmetic preprocessor's planted column.
  have hPreScalar : ∀ (κ : ℕ) (w : MddhAdvice p d ℓ κ) (pp : PublicParams G κ)
      (ab rs : Fin 2 → ZMod pp.group.order) (t : ZMod pp.group.order) (real : Bool),
      let castScalar := ZMod.ringEquivCongr (order_eq_of_publicParams G p hp κ pp).symm
      let L : Matrix (Fin (ℓ.eval κ)) (Fin 3) (ZMod pp.group.order) :=
        fun i j => castScalar (w.2.1 i j)
      let S : Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order) :=
        fun i j => castScalar (w.2.2.1 i j)
      let U : Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order) :=
        fun i j => castScalar (w.2.2.2 i j)
      let A0 : Matrix (Fin 3) (Fin 2) (ZMod pp.group.order) :=
        ![![ab 0, 0], ![0, ab 1], ![1, 1]]
      let v0 : Fin 3 → ZMod pp.group.order :=
        ![ab 0 * rs 0, ab 1 * rs 1, if real then rs 0 + rs 1 else t]
      G.mddhPreChallenge p hp d ℓ κ w
          (G.dlinChallenge κ pp (pp.generator ^ (ab 0).val) (pp.generator ^ (ab 1).val)
            (pp.generator ^ (ab 0 * rs 0).val) (pp.generator ^ (ab 1 * rs 1).val)
            (pp.generator ^ (if real then rs 0 + rs 1 else t).val)) =
        ⟨pp, pp.group.expMat pp.generator (L * A0),
          pp.group.expMat pp.generator (fun i j =>
            if j.val = w.1.val then Matrix.mulVec L v0 i
            else if j.val < w.1.val then ((L * A0) * S) i j else U i j)⟩ := sorry
  -- Fill these from the canonical ColumnLaws, hPreScalar, fixed-order transport and resampling.
  have hRealClose : ∀ (κ : ℕ) (j : Fin (d.eval κ)),
      |accept (hybrid κ (j.val + 1)) -
        avgTape κ (fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) true))| ≤
          1 / (p κ : ℝ) ^ 2 := sorry
  have hRandomClose : ∀ (κ : ℕ) (j : Fin (d.eval κ)),
      |accept (hybrid κ j.val) -
        avgTape κ (fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) false))| ≤
          1 - (1 - 1 / (p κ : ℝ)) ^ 3 := sorry
  have hLossBudget : ∀ κ,
      1 / (p κ : ℝ) ^ 2 + (1 - (1 - 1 / (p κ : ℝ)) ^ 3) ≤
        4 / (p κ : ℝ) := sorry
  have hMeanComparison (κ : ℕ) (j : Fin (d.eval κ)) :
      advantage (hybrid κ j.val) (hybrid κ (j.val + 1)) ≤
        avgTape κ (fun τ : Tape κ => redGap κ (j.castSucc, τ)) + 4 / (p κ : ℝ) := ?_
  swap
  · letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
    let a0 := accept (hybrid κ j.val)
    let a1 := accept (hybrid κ (j.val + 1))
    let r0 := avgTape κ (fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) false))
    let r1 := avgTape κ (fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) true))
    have hAvgGap : |r0 - r1| ≤
        avgTape κ (fun τ : Tape κ => redGap κ (j.castSucc, τ)) :=
      ProbComp.abs_expect_sub_le_expect (ProbComp.sample (Tape κ))
        (f := fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) false))
        (g := fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) true))
        (h := fun τ : Tape κ => redGap κ (j.castSucc, τ))
        (fun τ => (advantage_eq (redGame κ (j.castSucc, τ) false)
          (redGame κ (j.castSucc, τ) true)).symm.le)
    have hC0 : |a0 - r0| ≤ 1 - (1 - 1 / (p κ : ℝ)) ^ 3 := hRandomClose κ j
    have hC1 : |a1 - r1| ≤ 1 / (p κ : ℝ) ^ 2 := hRealClose κ j
    rw [abs_sub_comm] at hC1
    have hTriangle0 := abs_sub_le a0 r0 a1
    have hTriangle1 := abs_sub_le r0 r1 a1
    rw [advantage_eq]
    change |a0 - a1| ≤
      avgTape κ (fun τ : Tape κ => redGap κ (j.castSucc, τ)) + 4 / (p κ : ℝ)
    linarith only [hTriangle0, hTriangle1, hC0, hC1, hAvgGap, hLossBudget κ]
  -- Select finite advice at each parameter before any realiser is introduced.
  have hPointwise : ∀ κ, ∃ w : MddhAdvice p d ℓ κ,
      G.mddhAdv d ℓ D κ ≤ (d.eval κ : ℝ) * redGap κ w + mddhSlack p d κ := ?_
  swap
  · intro κ
    letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
    by_cases hd : d.eval κ = 0
    · refine ⟨mddhAdviceDefault p d ℓ κ, ?_⟩
      have hZero : G.mddhAdv d ℓ D κ = 0 := ?_
      swap
      · rw [hEndpointGap κ, hd, advantage_eq, sub_self, abs_zero]
      simpa only [hZero, mddhSlack_eq, hd, Nat.cast_zero, zero_mul, zero_add] using
        (le_refl (0 : ℝ))
    · have hdpos : 0 < d.eval κ := Nat.pos_of_ne_zero hd
      have hdR : 0 < (d.eval κ : ℝ) := Nat.cast_pos.mpr hdpos
      obtain ⟨j, hj, hgap⟩ := exists_advantage_hybrid_gap (hybrid κ) hdpos
      let i : Fin (d.eval κ) := ⟨j, hj⟩
      let f : Tape κ → ℝ := fun τ => redGap κ (i.castSucc, τ)
      obtain ⟨τ, hτ⟩ :=
        TCSlib.Cryptography.Authentication.LamportReduction.exists_expect_sample_le f
      refine ⟨(i.castSucc, τ), ?_⟩
      rw [← hEndpointGap κ] at hgap
      have hScaled : G.mddhAdv d ℓ D κ ≤
          (d.eval κ : ℝ) * advantage (hybrid κ i.val) (hybrid κ (i.val + 1)) := ?_
      swap
      · simpa only [mul_comm] using (div_le_iff₀ hdR).mp hgap
      have hPicked : avgTape κ f ≤ redGap κ (i.castSucc, τ) := hτ
      calc
        G.mddhAdv d ℓ D κ ≤
            (d.eval κ : ℝ) * advantage (hybrid κ i.val) (hybrid κ (i.val + 1)) := hScaled
        _ ≤ (d.eval κ : ℝ) * (avgTape κ f + 4 / (p κ : ℝ)) :=
          mul_le_mul_of_nonneg_left (hMeanComparison κ i) (Nat.cast_nonneg _)
        _ ≤ (d.eval κ : ℝ) * (redGap κ (i.castSucc, τ) + 4 / (p κ : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add_right hPicked (4 / (p κ : ℝ)))
            (Nat.cast_nonneg _)
        _ = (d.eval κ : ℝ) * redGap κ (i.castSucc, τ) + mddhSlack p d κ := ?_
      rw [mddhSlack_eq, mul_add]
  let ω : ∀ κ, MddhAdvice p d ℓ κ := fun κ => Classical.choose (hPointwise κ)
  have hω : ∀ κ,
      G.mddhAdv d ℓ D κ ≤ (d.eval κ : ℝ) * redGap κ (ω κ) + mddhSlack p d κ :=
    fun κ => Classical.choose_spec (hPointwise κ)
  refine ⟨ω, ?_⟩
  intro B hB κ
  -- This local coin identity reads the existing length-limited reduction; no machine is built.
  have hCoinUnwrap : ∀ (c : G.DLINChallenge κ) (ρ : B.Coins κ),
      decide (G.dlinToMddh p hp d ℓ D ω κ c (List.ofFn ρ) = [true]) =
        D.distinguisherL κ (G.mddhPre p hp d ℓ κ (ω κ) c)
          (NUPPT.coinsCongr (A := B) (B := D) hB.coins_eq κ ρ) := sorry
  have hCoinVerdict (c : G.DLINChallenge κ) (ρ : B.Coins κ) :
      B.distinguisherL κ (G.dlinEnc κ c) ρ =
        D.distinguisherL κ (G.mddhPre p hp d ℓ κ (ω κ) c)
          (NUPPT.coinsCongr (A := B) (B := D) hB.coins_eq κ ρ) :=
    (hB.distinguisherL_eq κ c ρ).trans (hCoinUnwrap c ρ)
  have hAccept (real : Bool) :
      accept (G.dlinGame B real κ) = accept (redGame κ (ω κ) real) := ?_
  swap
  · rw [accept_eq (G.dlinGame B real κ), G.dlinGame_eq B real κ, ProbComp.prob_bind]
    dsimp only [redGame]
    rw [accept_eq, ProbComp.prob_bind]
    apply congrArg (ProbComp.expect (G.dlinSample real κ))
    funext c
    simp only [ProbComp.prob_bind, ProbComp.prob_pure]
    rw [← ProbComp.expect_sample_equiv (NUPPT.coinsCongr (A := B) (B := D) hB.coins_eq κ)
      (fun ρ : D.Coins κ =>
        if D.distinguisherL κ (G.mddhPre p hp d ℓ κ (ω κ) c) ρ = true
        then (1 : ℝ) else 0)]
    apply congrArg (ProbComp.expect (ProbComp.sample (B.Coins κ)))
    funext ρ
    rw [hCoinVerdict c ρ]
  have hGap : redGap κ (ω κ) = G.dlinAdv B κ := ?_
  swap
  · dsimp only [redGap]
    rw [G.dlinAdv_eq B κ, advantage_eq, advantage_eq, hAccept false, hAccept true]
  calc
    G.mddhAdv d ℓ D κ ≤ (d.eval κ : ℝ) * redGap κ (ω κ) + mddhSlack p d κ := hω κ
    _ = (d.eval κ : ℝ) * G.dlinAdv B κ + mddhSlack p d κ :=
      congrArg (fun x : ℝ => (d.eval κ : ℝ) * x + mddhSlack p d κ) hGap
