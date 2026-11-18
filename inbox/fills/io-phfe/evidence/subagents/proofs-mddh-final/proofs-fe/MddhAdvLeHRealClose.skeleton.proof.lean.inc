by
    intro κ j
    letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
    let SType (pp : PublicParams G κ) : Type :=
      Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order)
    let UType (pp : PublicParams G κ) : Type :=
      Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order)
    let A0 (pp : PublicParams G κ) (ab : Fin 2 → ZMod pp.group.order) :
        Matrix (Fin 3) (Fin 2) (ZMod pp.group.order) :=
      ![![ab 0, 0], ![0, ab 1], ![1, 1]]
    -- Keep every unselected column and the original distinguisher coins in the test.
    let obs (pp : PublicParams G κ) (S : SType pp) (U : UType pp)
        (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order))
        (v : Fin (ℓ.eval κ) → ZMod pp.group.order) : ℝ :=
      ProbComp.prob (ProbComp.sample (D.Coins κ)) fun r =>
        D.distinguisherL κ (G.mddhEnc d ℓ κ
          ⟨pp, pp.group.expMat pp.generator M,
            pp.group.expMat pp.generator (fun a b =>
              if b.val = j.val then v a
              else if b.val < j.val then (M * S) a b else U a b)⟩) r = true
    let idealCore (pp : PublicParams G κ) (S : SType pp) (U : UType pp) : ℝ :=
      ProbComp.expect
        (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)))
        fun M => ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order))
          fun rs => obs pp S U M (Matrix.mulVec M rs)
    let plantedCore (pp : PublicParams G κ) (S : SType pp) (U : UType pp) : ℝ :=
      ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)) fun ab =>
        ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)) fun rs =>
          ProbComp.expect
            (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 3) (ZMod pp.group.order)))
            fun L => obs pp S U (L * A0 pp ab)
              (Matrix.mulVec L (Matrix.mulVec (A0 pp ab) rs))
    let ideal (pp : PublicParams G κ) : ℝ :=
      ProbComp.expect (ProbComp.sample (SType pp)) fun S =>
        ProbComp.expect (ProbComp.sample (UType pp)) (idealCore pp S)
    let planted (pp : PublicParams G κ) : ℝ :=
      ProbComp.expect (ProbComp.sample (SType pp)) fun S =>
        ProbComp.expect (ProbComp.sample (UType pp)) (plantedCore pp S)
    -- Move the advice sample through pp and transport its scalar coordinates by the
    -- published order equality. Read the actual reduction with hPreScalar; integrate
    -- its original unused final scalar, without changing the underlying DLIN draw.
    have hReductionTransport :
        avgTape κ (fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) true)) =
          ProbComp.expect (publicParamsGen G κ) planted := sorry
    -- Transpose S to a tuple of whole columns. The selected column can be sampled
    -- apart with expect_sample_coord because obs ignores that coordinate of S.
    -- Retain U and all unused S coordinates; no conditional or restricted draw appears.
    have hHybridResample :
        accept (hybrid κ (j.val + 1)) =
          ProbComp.expect (publicParamsGen G κ) ideal := sorry
    -- Apply the already-proved scalar column law, with the observer bounded as a probability.
    have hCorePoint (pp : PublicParams G κ) (S : SType pp) (U : UType pp) :
        |idealCore pp S U - plantedCore pp S U| ≤ 1 / (p κ : ℝ) ^ 2 := ?_
    swap
    · letI : Fact pp.group.order.Prime := ⟨pp.group.order_prime⟩
      letI : NeZero pp.group.order := ⟨pp.group.order_prime.ne_zero⟩
      have h0 : ∀ M v, 0 ≤ obs pp S U M v :=
        fun M v => ProbComp.prob_nonneg (ProbComp.sample (D.Coins κ)) _
      have h1 : ∀ M v, obs pp S U M v ≤ 1 :=
        fun M v => ProbComp.prob_le_one (ProbComp.sample (D.Coins κ)) _
      have h := dlin_real_column_gap_le (K := ZMod pp.group.order)
        (ℓ.eval κ) (obs pp S U) h0 h1
      have hCard : Fintype.card (ZMod pp.group.order) = p κ :=
        (ZMod.card pp.group.order).trans (order_eq_of_publicParams G p hp κ pp)
      change |plantedCore pp S U - idealCore pp S U| ≤
        1 / (Fintype.card (ZMod pp.group.order) : ℝ) ^ 2 at h
      rw [hCard] at h
      rw [abs_sub_comm]
      exact h
    -- Uniform expectations preserve a constant gap; use the existing averaging law
    -- at each of the two untouched tape blocks, then at public-parameter generation.
    have hPoint (pp : PublicParams G κ) :
        |ideal pp - planted pp| ≤ 1 / (p κ : ℝ) ^ 2 :=
      ProbComp.abs_expect_sub_le (ProbComp.sample (SType pp))
        (f := fun S => ProbComp.expect (ProbComp.sample (UType pp)) (idealCore pp S))
        (g := fun S => ProbComp.expect (ProbComp.sample (UType pp)) (plantedCore pp S))
        (fun S => ProbComp.abs_expect_sub_le (ProbComp.sample (UType pp))
          (f := idealCore pp S) (g := plantedCore pp S) (fun U => hCorePoint pp S U))
    rw [hHybridResample, hReductionTransport]
    exact ProbComp.abs_expect_sub_le (publicParamsGen G κ)
      (f := ideal) (g := planted) hPoint
