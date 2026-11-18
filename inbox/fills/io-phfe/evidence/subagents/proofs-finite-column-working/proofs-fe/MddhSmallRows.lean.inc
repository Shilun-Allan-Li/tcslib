/-- With at most two rows the matrix assumption is statistical, with the explicit
rank-deficiency bound averaged over the public group draw
[Wee20, §2.1, p. 4, paragraph after Assumption 1].

**Proof sketch.** Condition on the uniform base matrix having full row rank. Then its map
from two scalar coordinates onto the row space is surjective and sends uniform independent
coefficient columns to uniform response columns. The failure probability for zero, one,
or two rows is at most `2/p`; bound the distinguisher's gap by that event probability. -/
theorem mddhAdv_smallRows_le (d ℓ : PolyExpr) (D : NUPPT)
    (hℓ : ∀ κ, ℓ.eval κ ≤ 2) (κ : ℕ) :
    G.mddhAdv d ℓ D κ ≤
      ProbComp.expect (ProbComp.sample (G.gen.Coins κ))
        (fun r => 2 / ((G.inst κ r).order : ℝ)) := by
  classical
  let H (pp : PublicParams G κ)
      (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order))
      (U : Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order)) : ℝ :=
    ProbComp.prob (ProbComp.sample (D.Coins κ)) fun r =>
      D.distinguisherL κ (G.mddhEnc d ℓ κ
        ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator U⟩) r = true
  let P (pp : PublicParams G κ)
      (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)) : ℝ :=
    ProbComp.expect
      (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order)))
      (H pp M)
  let Q (pp : PublicParams G κ)
      (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)) : ℝ :=
    ProbComp.expect
      (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order)))
      (fun S => H pp M (M * S))
  let good (pp : PublicParams G κ)
      (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)) : Prop :=
    Function.Surjective (Matrix.mulVec M)
  -- The actual distinguisher test and both conditional averages take values in [0, 1].
  have hP0 : ∀ pp M, 0 ≤ P pp M := ?_
  swap
  · intro pp M
    letI : Fact pp.group.order.Prime := ⟨pp.group.order_prime⟩
    letI : NeZero pp.group.order := ⟨pp.group.order_prime.ne_zero⟩
    exact ProbComp.expect_nonneg
      (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order)))
      (fun U => ProbComp.prob_nonneg (ProbComp.sample (D.Coins κ))
        (fun r : D.Coins κ => D.distinguisherL κ (G.mddhEnc d ℓ κ
          ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator U⟩) r = true))
  have hP1 : ∀ pp M, P pp M ≤ 1 := ?_
  swap
  · intro pp M
    letI : Fact pp.group.order.Prime := ⟨pp.group.order_prime⟩
    letI : NeZero pp.group.order := ⟨pp.group.order_prime.ne_zero⟩
    calc
      P pp M ≤ ProbComp.expect
          (ProbComp.sample
            (Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order)))
          (fun _ => 1) :=
        ProbComp.expect_mono
          (ProbComp.sample
            (Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order)))
          (fun U => ProbComp.prob_le_one (ProbComp.sample (D.Coins κ))
            (fun r : D.Coins κ => D.distinguisherL κ (G.mddhEnc d ℓ κ
              ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator U⟩)
              r = true))
      _ = 1 := ProbComp.expect_const
        (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order))) 1
  have hQ0 : ∀ pp M, 0 ≤ Q pp M := ?_
  swap
  · intro pp M
    letI : Fact pp.group.order.Prime := ⟨pp.group.order_prime⟩
    letI : NeZero pp.group.order := ⟨pp.group.order_prime.ne_zero⟩
    exact ProbComp.expect_nonneg
      (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order)))
      (fun S => ProbComp.prob_nonneg (ProbComp.sample (D.Coins κ))
        (fun r : D.Coins κ => D.distinguisherL κ (G.mddhEnc d ℓ κ
          ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator (M * S)⟩)
          r = true))
  have hQ1 : ∀ pp M, Q pp M ≤ 1 := ?_
  swap
  · intro pp M
    letI : Fact pp.group.order.Prime := ⟨pp.group.order_prime⟩
    letI : NeZero pp.group.order := ⟨pp.group.order_prime.ne_zero⟩
    calc
      Q pp M ≤ ProbComp.expect
          (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order)))
          (fun _ => 1) :=
        ProbComp.expect_mono
          (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order)))
          (fun S => ProbComp.prob_le_one (ProbComp.sample (D.Coins κ))
            (fun r : D.Coins κ => D.distinguisherL κ (G.mddhEnc d ℓ κ
              ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator (M * S)⟩)
              r = true))
      _ = 1 := ProbComp.expect_const
        (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order))) 1
  -- On a surjective base matrix, the whole response matrix has exactly the uniform law.
  have hUniform : ∀ pp M, good pp M → P pp M = Q pp M := ?_
  swap
  · intro pp M hM
    letI : Fact pp.group.order.Prime := ⟨pp.group.order_prime⟩
    letI : NeZero pp.group.order := ⟨pp.group.order_prime.ne_zero⟩
    exact (expect_sample_matrix_mul_of_mulVec_surjective
      (K := ZMod pp.group.order) (r := ℓ.eval κ) (m := 2) (c := d.eval κ)
      M hM (H pp M)).symm
  have hFailure : ∀ pp : PublicParams G κ,
      ProbComp.expect
          (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)))
          (fun M => if good pp M then (0 : ℝ) else 1) ≤
        2 / (pp.group.order : ℝ) := ?_
  swap
  · intro pp
    letI : Fact pp.group.order.Prime := ⟨pp.group.order_prime⟩
    letI : NeZero pp.group.order := ⟨pp.group.order_prime.ne_zero⟩
    have h := smallRows_surjectivity_failure_le
      (K := ZMod pp.group.order) (ℓ.eval κ) (hℓ κ)
    rw [ProbComp.prob_eq_expect
      (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)))
      (fun M : Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order) =>
        ¬ Function.Surjective (Matrix.mulVec M))] at h
    simpa only [good, ite_not, ZMod.card] using h
  -- The gap vanishes on good bases and is at most one on the rank-failure event.
  have hEntry : ∀ pp M, |P pp M - Q pp M| ≤ if good pp M then (0 : ℝ) else 1 := ?_
  swap
  · intro pp M
    by_cases hg : good pp M
    · simpa only [if_pos hg, hUniform pp M hg, sub_self, abs_zero] using
        (le_refl (0 : ℝ))
    · rw [if_neg hg, abs_le]
      constructor <;> linarith [hP0 pp M, hP1 pp M, hQ0 pp M, hQ1 pp M]
  have hPoint (pp : PublicParams G κ) :
      |ProbComp.expect
            (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)))
            (P pp) -
          ProbComp.expect
            (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)))
            (Q pp)| ≤ 2 / (pp.group.order : ℝ) :=
    (ProbComp.abs_expect_sub_le_expect
      (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)))
      (f := P pp) (g := Q pp)
      (h := fun M => if good pp M then (0 : ℝ) else 1) (hEntry pp)).trans (hFailure pp)
  -- The loss depends only on the generated description, not on the fresh generator draw.
  have hLoss :
      ProbComp.expect (publicParamsGen G κ) (fun pp => 2 / (pp.group.order : ℝ)) =
        ProbComp.expect (ProbComp.sample (G.gen.Coins κ))
          (fun r => 2 / ((G.inst κ r).order : ℝ)) := ?_
  swap
  · rw [publicParamsGen_eq G κ, ProbComp.expect_bind]
    apply congrArg (ProbComp.expect (ProbComp.sample (G.gen.Coins κ)))
    funext ρ
    let desc : GroupDescription G κ := ⟨G.desc κ ρ, ⟨ρ, rfl⟩⟩
    change ProbComp.expect
        (publicParamsCore G κ desc <$> ProbComp.sample (GeneratorDraw G κ desc))
        (fun pp : PublicParams G κ => 2 / (pp.group.order : ℝ)) =
      2 / ((G.inst κ ρ).order : ℝ)
    rw [ProbComp.expect_map, G.inst_eq κ ρ]
    have hOrder (g : GeneratorDraw G κ desc) :
        (publicParamsCore G κ desc g).group.order = (G.group κ desc.val).order := ?_
    swap
    · rw [PublicParams.group_eq (publicParamsCore G κ desc g),
        publicParamsCore_eq G κ desc g]
    have hIntegrand :
        (fun g : GeneratorDraw G κ desc =>
          2 / ((publicParamsCore G κ desc g).group.order : ℝ)) =
          (fun _ => 2 / ((G.group κ desc.val).order : ℝ)) :=
      funext (fun g => congrArg (fun n : ℕ => 2 / (n : ℝ)) (hOrder g))
    rw [hIntegrand]
    exact ProbComp.expect_const (ProbComp.sample (GeneratorDraw G κ desc))
      (2 / ((G.group κ desc.val).order : ℝ))
  -- Read each actual game, keeping the encoded distinguisher leaf opaque.
  have hAccept (real : Bool) :
      accept (G.mddhGame d ℓ D real κ) =
        ProbComp.expect (publicParamsGen G κ) (fun pp =>
          ProbComp.expect
            (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)))
            (fun M => if real then Q pp M else P pp M)) := ?_
  swap
  · rw [accept_eq (G.mddhGame d ℓ D real κ), G.mddhGame_eq d ℓ D real κ,
      ProbComp.prob_bind, G.mddhSample_eq d ℓ real κ, ProbComp.expect_bind]
    apply congrArg (ProbComp.expect (publicParamsGen G κ))
    funext pp
    letI : Fact pp.group.order.Prime := ⟨pp.group.order_prime⟩
    letI : NeZero pp.group.order := ⟨pp.group.order_prime.ne_zero⟩
    rw [ProbComp.expect_bind]
    apply congrArg
      (ProbComp.expect
        (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order))))
    funext M
    have hVerdict
        (U : Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order)) :
        ProbComp.prob ((ProbComp.sample (D.Coins κ)).bind fun r =>
          .pure (D.distinguisherL κ (G.mddhEnc d ℓ κ
            ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator U⟩) r))
          (fun b => b = true) = H pp M U := ?_
    swap
    · change ProbComp.prob ((ProbComp.sample (D.Coins κ)).bind fun r =>
          .pure (D.distinguisherL κ (G.mddhEnc d ℓ κ
            ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator U⟩) r))
          (fun b => b = true) =
        ProbComp.prob (ProbComp.sample (D.Coins κ))
          (fun r : D.Coins κ => D.distinguisherL κ (G.mddhEnc d ℓ κ
            ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator U⟩) r = true)
      rw [ProbComp.prob_eq_expect (ProbComp.sample (D.Coins κ))
        (fun r : D.Coins κ => D.distinguisherL κ (G.mddhEnc d ℓ κ
          ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator U⟩) r = true),
        ProbComp.prob_bind]
      apply congrArg (ProbComp.expect (ProbComp.sample (D.Coins κ)))
      funext r
      exact ProbComp.prob_pure
        (D.distinguisherL κ (G.mddhEnc d ℓ κ
          ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator U⟩) r)
        (fun b => b = true)
    simp only [ProbComp.expect_bind, ProbComp.expect_pure, hVerdict]
    cases real
    · simp only [Bool.false_eq_true, if_false]
      exact ProbComp.expect_const
        (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order))) (P pp M)
    · simp only [Bool.true_eq_true, if_true]
      change ProbComp.expect
          (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order)))
          (fun S => ProbComp.expect
            (ProbComp.sample
              (Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order)))
            (fun _ => H pp M (M * S))) =
        ProbComp.expect
          (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order)))
          (fun S => H pp M (M * S))
      apply congrArg
        (ProbComp.expect
          (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order))))
      funext S
      exact ProbComp.expect_const
        (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order)))
        (H pp M (M * S))
  have hAverage := ProbComp.abs_expect_sub_le_expect (publicParamsGen G κ)
    (f := fun pp => ProbComp.expect
      (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order))) (P pp))
    (g := fun pp => ProbComp.expect
      (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order))) (Q pp))
    (h := fun pp => 2 / (pp.group.order : ℝ)) hPoint
  rw [hLoss] at hAverage
  rw [G.mddhAdv_eq d ℓ D κ, advantage_eq, hAccept false, hAccept true]
  simpa only [Bool.false_eq_true, Bool.true_eq_true, if_false, if_true] using hAverage
