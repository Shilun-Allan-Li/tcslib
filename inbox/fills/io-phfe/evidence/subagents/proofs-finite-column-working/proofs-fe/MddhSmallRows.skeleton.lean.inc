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
  have hP0 : ∀ pp M, 0 ≤ P pp M :=
    fun pp M => ProbComp.expect_nonneg _ (fun U => ProbComp.prob_nonneg _ _)
  have hP1 : ∀ pp M, P pp M ≤ 1 :=
    fun pp M =>
      calc
        P pp M ≤ ProbComp.expect
            (ProbComp.sample
              (Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order)))
            (fun _ => 1) :=
          ProbComp.expect_mono _ (fun U => ProbComp.prob_le_one _ _)
        _ = 1 := ProbComp.expect_const _ 1
  have hQ0 : ∀ pp M, 0 ≤ Q pp M :=
    fun pp M => ProbComp.expect_nonneg _ (fun S => ProbComp.prob_nonneg _ _)
  have hQ1 : ∀ pp M, Q pp M ≤ 1 :=
    fun pp M =>
      calc
        Q pp M ≤ ProbComp.expect
            (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order)))
            (fun _ => 1) :=
          ProbComp.expect_mono _ (fun S => ProbComp.prob_le_one _ _)
        _ = 1 := ProbComp.expect_const _ 1
  have hUniform : ∀ pp M, good pp M → P pp M = Q pp M := sorry
  have hFailure : ∀ pp : PublicParams G κ,
      ProbComp.expect
          (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)))
          (fun M => if good pp M then (0 : ℝ) else 1) ≤
        2 / (pp.group.order : ℝ) := sorry
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
    (ProbComp.abs_expect_sub_le_expect _ (hEntry pp)).trans (hFailure pp)
  have hLoss :
      ProbComp.expect (publicParamsGen G κ) (fun pp => 2 / (pp.group.order : ℝ)) =
        ProbComp.expect (ProbComp.sample (G.gen.Coins κ))
          (fun r => 2 / ((G.inst κ r).order : ℝ)) := ?_
  swap
  · simp only [publicParamsGen_eq, ProbComp.expect_bind, ProbComp.expect_map,
      publicParamsCore_eq, ProbComp.expect_const, G.inst_eq]
  have hAverage := ProbComp.abs_expect_sub_le_expect (publicParamsGen G κ) hPoint
  rw [hLoss] at hAverage
  simpa only [P, Q, H, mddhAdv_eq, advantage_eq, accept_eq, mddhGame_eq, mddhSample_eq,
    ProbComp.prob_bind, ProbComp.expect_bind, ProbComp.expect_pure, ProbComp.prob_pure,
    ProbComp.prob_eq_expect, ↓reduceIte, ProbComp.expect_const] using hAverage
