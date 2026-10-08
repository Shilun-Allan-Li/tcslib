/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Symmetrization and randomization of random variables

## Main definitions

The probability-space definitions are in `RandomVariablesBasic`.

## Main results

* `symmetrization_norm_le`: subtracting an independent centered copy increases affine norms.
* `randomization_norm_le`: randomizing by an independent sign controls the half-scaled norm.
  Both bounds include the essential-supremum exponent.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §10.2, Lemmas 10.14–10.15.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.Hypercontractivity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Subtracting an independent copy of a centered variable increases the norm of any
affine translate, for every exponent at least one. [OD14, Lem. 10.14]
The extended-exponent formulation also includes the essential-supremum endpoint.

**Proof sketch.** Independence identifies the joint law with the product of the marginal
law. For each fixed original value, averaging over the centered copy recovers the translate.
Bound the norm of this average by its `L¹` norm and then its `L^q` norm. Integrate the
`q`th powers; at infinity, use the corresponding almost-everywhere bound. -/
theorem symmetrization_norm_le (X X' : Ω → ℝ) (q : ℝ≥0∞) (a : ℝ)
    (hq : 1 ≤ q) (hmem : MemLp X q μ) (hmean : ∫ ω, X ω ∂μ = 0)
    (hcopy : IdentDistrib X X' μ μ) (hindep : IndepFun X X' μ) :
    eLpNorm (fun ω => a + X ω) q μ ≤ eLpNorm (fun ω => a + X ω - X' ω) q μ := (by
  let ν := μ.map X
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hcopy.aemeasurable_fst
  have hν : MemLp (fun x : ℝ => x) q ν :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable
      hcopy.aemeasurable_fst).2 hmem
  have hνmean : (∫ x : ℝ, x ∂ν) = 0 :=
    (integral_map hcopy.aemeasurable_fst
      measurable_id.aestronglyMeasurable).trans hmean
  have hpair : μ.map (fun ω => (X ω, X' ω)) = ν.prod ν := by
    simpa only [ν, ← hcopy.map_eq] using
      (indepFun_iff_map_prod_eq_prod_map_map
        hcopy.aemeasurable_fst hcopy.aemeasurable_snd).mp hindep
  have hslice (x : ℝ) :
      ‖a + x‖ₑ ≤ eLpNorm (fun y : ℝ => a + x - y) q ν := by
    calc
      _ = ‖∫ y : ℝ, a + x - y ∂ν‖ₑ := by
        rw [integral_sub (integrable_const _) (MemLp.integrable hq hν), hνmean]
        simp
      _ ≤ ∫⁻ y : ℝ, ‖a + x - y‖ₑ ∂ν :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ eLpNorm (fun y : ℝ => a + x - y) q ν := by
        rw [← eLpNorm_one_eq_lintegral_enorm]
        exact eLpNorm_le_eLpNorm_of_exponent_le hq (by fun_prop)
  calc
    _ = eLpNorm (fun x : ℝ => a + x) q ν :=
      (eLpNorm_map_measure (by fun_prop) hcopy.aemeasurable_fst).symm
    _ ≤ eLpNorm (fun z : ℝ × ℝ => a + z.1 - z.2) q (ν.prod ν) := by
      by_cases hqtop : q = ∞
      · subst q
        simp only [eLpNorm_exponent_top] at hslice ⊢
        apply eLpNormEssSup_le_of_ae_enorm_bound
        filter_upwards [Measure.ae_ae_of_ae_prod
          (ae_le_eLpNormEssSup
            (f := fun z : ℝ × ℝ => a + z.1 - z.2)
            (μ := ν.prod ν))] with x hx
        exact (hslice x).trans (eLpNormEssSup_le_of_ae_enorm_bound hx)
      · have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
        have hqpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
        rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop,
          eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop]
        apply ENNReal.rpow_le_rpow ?_ (by positivity)
        rw [lintegral_prod _ (by fun_prop)]
        apply lintegral_mono
        intro x
        calc
          ‖a + x‖ₑ ^ q.toReal ≤
              (eLpNorm (fun y : ℝ => a + x - y) q ν) ^ q.toReal :=
            ENNReal.rpow_le_rpow (hslice x) hqpos.le
          _ = ∫⁻ y : ℝ, ‖a + x - y‖ₑ ^ q.toReal ∂ν := by
            rw [eLpNorm_eq_eLpNorm' hq0 hqtop,
              lintegral_rpow_enorm_eq_rpow_eLpNorm' hqpos]
    _ = _ := by
      rw [← hpair]
      exact eLpNorm_map_measure (by fun_prop)
        (hcopy.aemeasurable_fst.prodMk hcopy.aemeasurable_snd)
)


/-- Randomizing a centered variable by an independent uniform sign dominates the norm of
the same translate with its random part halved. [OD14, Lem. 10.15]
The extended-exponent formulation includes the essential-supremum endpoint.

**Proof sketch.** Centering bounds the constant term by the norm of the negative translate.
Apply the triangle inequality to half the positive translate plus half the constant, then
the power-mean inequality to the two translate norms. Independence and the uniform sign law
identify the resulting bound with the randomized norm. At infinity, use their maximum. -/
theorem randomization_norm_le (X r : Ω → ℝ) (q : ℝ≥0∞) (a : ℝ)
    (hq : 1 ≤ q) (hmem : MemLp X q μ) (hmean : ∫ ω, X ω ∂μ = 0)
    (hr : IsRademacherRV r μ) (hindep : IndepFun X r μ) :
    eLpNorm (fun ω => a + (1 / 2 : ℝ) * X ω) q μ ≤
      eLpNorm (fun ω => a + r ω * X ω) q μ := (by
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
  have hX : AEMeasurable X μ := hmem.1.aemeasurable
  let ν : Measure ℝ := μ.map X
  let R : Measure ℝ :=
    (1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ) +
      (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hX
  -- Transfer the centered variable to its law on the real line.
  have hid : MemLp (fun x : ℝ => x) q ν :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable hX).2 hmem
  have hmeanν : (∫ x : ℝ, x ∂ν) = 0 := by
    calc
      (∫ x : ℝ, x ∂ν) = ∫ ω, X ω ∂μ :=
        integral_map hX measurable_id.aestronglyMeasurable
      _ = 0 := hmean
  -- The independent sign has the uniform law on the two signs.
  have hrlaw : μ.map r = R := hr.map_eq
  haveI : IsProbabilityMeasure R := by
    rw [← hrlaw]
    exact Measure.isProbabilityMeasure_map hr.1.aemeasurable
  have hpair : μ.map (fun ω => (X ω, r ω)) = ν.prod R := by
    simpa only [ν, hrlaw] using
      (indepFun_iff_map_prod_eq_prod_map_map hX hr.1.aemeasurable).mp hindep
  let plus : ℝ → ℝ := fun x => a + x
  let minus : ℝ → ℝ := fun x => a - x
  let F : ℝ × ℝ → ℝ := fun z => a + z.2 * z.1
  let P := eLpNorm plus q ν
  let M := eLpNorm minus q ν
  let B := eLpNorm F q (ν.prod R)
  have hplus : Measurable plus := by fun_prop
  have hminus : Measurable minus := by fun_prop
  have hF : Measurable F := by fun_prop
  -- Centering bounds the constant by the negative profile.
  have hmeanminus : (∫ x : ℝ, minus x ∂ν) = a := by
    dsimp [minus]
    rw [integral_sub (integrable_const a) (MemLp.integrable hq hid)]
    simp [hmeanν]
  have hcenter : eLpNorm (fun _ : ℝ => a) q ν ≤ M := by
    calc
      eLpNorm (fun _ : ℝ => a) q ν = ‖a‖ₑ := by
        rw [eLpNorm_const a hq0 (NeZero.ne ν)]
        simp
      _ = ‖∫ x : ℝ, minus x ∂ν‖ₑ := by rw [hmeanminus]
      _ ≤ ∫⁻ x : ℝ, ‖minus x‖ₑ ∂ν :=
        enorm_integral_le_lintegral_enorm minus
      _ = eLpNorm minus 1 ν := by
        rw [eLpNorm_one_eq_lintegral_enorm]
      _ ≤ M :=
        eLpNorm_le_eLpNorm_of_exponent_le hq hminus.aestronglyMeasurable
  have hhalf : ‖(1 / 2 : ℝ)‖ₑ = (1 / 2 : ℝ≥0∞) := by
    rw [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 : ℝ))]
    norm_num
  have htriangle :
      eLpNorm (fun x : ℝ => a + (1 / 2 : ℝ) * x) q ν ≤
        (1 / 2 : ℝ≥0∞) * P + (1 / 2 : ℝ≥0∞) * M := by
    calc
      eLpNorm (fun x : ℝ => a + (1 / 2 : ℝ) * x) q ν =
          eLpNorm ((1 / 2 : ℝ) • plus +
            (1 / 2 : ℝ) • (fun _ : ℝ => a)) q ν := by
        congr 1
        funext x
        simp only [Pi.add_apply, Pi.smul_apply, plus, smul_eq_mul]
        ring
      _ ≤ eLpNorm ((1 / 2 : ℝ) • plus) q ν +
          eLpNorm ((1 / 2 : ℝ) • (fun _ : ℝ => a)) q ν :=
        eLpNorm_add_le
          (hplus.aestronglyMeasurable.const_smul (1 / 2 : ℝ))
          ((aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : ℝ => a) ν).const_smul (1 / 2 : ℝ))
          hq
      _ = (1 / 2 : ℝ≥0∞) * P +
          (1 / 2 : ℝ≥0∞) * eLpNorm (fun _ : ℝ => a) q ν := by
        simp only [eLpNorm_const_smul, hhalf, P]
      _ ≤ (1 / 2 : ℝ≥0∞) * P + (1 / 2 : ℝ≥0∞) * M :=
        add_le_add_left (mul_le_mul_left' hcenter _) _
  -- The average of the two profile norms is bounded by the randomized norm.
  have hprofiles : (1 / 2 : ℝ≥0∞) * P + (1 / 2 : ℝ≥0∞) * M ≤ B := by
    by_cases hqtop : q = ∞
    · have hjoint : ∀ᵐ z ∂ν.prod R, ‖F z‖ₑ ≤ B := by
        simpa only [B, hqtop, eLpNorm_exponent_top] using
          (ae_le_eLpNormEssSup :
            ∀ᵐ z ∂ν.prod R, ‖F z‖ₑ ≤ eLpNormEssSup F (ν.prod R))
      have hboth :
          ∀ᵐ x ∂ν, ‖plus x‖ₑ ≤ B ∧ ‖minus x‖ₑ ≤ B := by
        filter_upwards [Measure.ae_ae_of_ae_prod hjoint] with x hx
        simpa [R, ae_add_measure_iff,
          Measure.ae_smul_measure_iff
            (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0),
          ae_dirac_eq, F, plus, minus, sub_eq_add_neg] using hx
      have hP : P ≤ B := by
        change eLpNorm plus q ν ≤ B
        rw [hqtop, eLpNorm_exponent_top]
        exact eLpNormEssSup_le_of_ae_enorm_bound (hboth.mono fun _ h => h.1)
      have hM : M ≤ B := by
        change eLpNorm minus q ν ≤ B
        rw [hqtop, eLpNorm_exponent_top]
        exact eLpNormEssSup_le_of_ae_enorm_bound (hboth.mono fun _ h => h.2)
      calc
        (1 / 2 : ℝ≥0∞) * P + (1 / 2 : ℝ≥0∞) * M ≤
            (1 / 2 : ℝ≥0∞) * B + (1 / 2 : ℝ≥0∞) * B :=
          add_le_add (mul_le_mul_left' hP _) (mul_le_mul_left' hM _)
        _ = B := by
          rw [← add_mul, ENNReal.add_halves, one_mul]
    · have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
      have hp1 : 1 ≤ q.toReal := by
        simpa using ENNReal.toReal_mono hqtop hq
      have hpower (f : ℝ → ℝ) :
          (eLpNorm f q ν) ^ q.toReal =
            ∫⁻ x : ℝ, ‖f x‖ₑ ^ q.toReal ∂ν := by
        rw [eLpNorm_eq_eLpNorm' hq0 hqtop]
        exact (lintegral_rpow_enorm_eq_rpow_eLpNorm' hp).symm
      have hBpower :
          B ^ q.toReal =
            (1 / 2 : ℝ≥0∞) * P ^ q.toReal +
              (1 / 2 : ℝ≥0∞) * M ^ q.toReal := by
        calc
          B ^ q.toReal = ∫⁻ z : ℝ × ℝ, ‖F z‖ₑ ^ q.toReal ∂ν.prod R := by
            dsimp [B]
            rw [eLpNorm_eq_eLpNorm' hq0 hqtop]
            exact (lintegral_rpow_enorm_eq_rpow_eLpNorm' hp).symm
          _ = ∫⁻ x : ℝ, ∫⁻ y : ℝ, ‖F (x, y)‖ₑ ^ q.toReal ∂R ∂ν :=
            lintegral_prod _ (by fun_prop)
          _ = ∫⁻ x : ℝ,
              (1 / 2 : ℝ≥0∞) * ‖plus x‖ₑ ^ q.toReal +
                (1 / 2 : ℝ≥0∞) * ‖minus x‖ₑ ^ q.toReal ∂ν := by
            congr 1
            funext x
            simp [R, lintegral_add_measure, lintegral_smul_measure,
              lintegral_dirac, F, plus, minus, sub_eq_add_neg]
          _ = (1 / 2 : ℝ≥0∞) * (∫⁻ x : ℝ, ‖plus x‖ₑ ^ q.toReal ∂ν) +
              (1 / 2 : ℝ≥0∞) * (∫⁻ x : ℝ, ‖minus x‖ₑ ^ q.toReal ∂ν) := by
            rw [lintegral_add_left
              (by fun_prop : Measurable (fun x : ℝ =>
                (1 / 2 : ℝ≥0∞) * ‖plus x‖ₑ ^ q.toReal))
              (fun x : ℝ => (1 / 2 : ℝ≥0∞) * ‖minus x‖ₑ ^ q.toReal),
              lintegral_const_mul (1 / 2 : ℝ≥0∞)
                (by fun_prop : Measurable (fun x : ℝ => ‖plus x‖ₑ ^ q.toReal)),
              lintegral_const_mul (1 / 2 : ℝ≥0∞)
                (by fun_prop : Measurable (fun x : ℝ => ‖minus x‖ₑ ^ q.toReal))]
          _ = (1 / 2 : ℝ≥0∞) * P ^ q.toReal +
              (1 / 2 : ℝ≥0∞) * M ^ q.toReal := by
            rw [← hpower plus, ← hpower minus]
      apply (ENNReal.rpow_le_rpow_iff hp).mp
      rw [hBpower]
      exact ENNReal.rpow_arith_mean_le_arith_mean2_rpow
        (1 / 2) (1 / 2) P M (ENNReal.add_halves (1 : ℝ≥0∞)) hp1
  -- Transfer the inequality back to the original probability space.
  calc
    eLpNorm (fun ω => a + (1 / 2 : ℝ) * X ω) q μ =
        eLpNorm (fun x : ℝ => a + (1 / 2 : ℝ) * x) q ν := by
      simpa only [ν, Function.comp_def] using
        (eLpNorm_map_measure (p := q)
          (by fun_prop : AEStronglyMeasurable
            (fun x : ℝ => a + (1 / 2 : ℝ) * x) ν) hX).symm
    _ ≤ (1 / 2 : ℝ≥0∞) * P + (1 / 2 : ℝ≥0∞) * M := htriangle
    _ ≤ B := hprofiles
    _ = eLpNorm (fun ω => a + r ω * X ω) q μ := by
      dsimp [B]
      rw [← hpair]
      simpa only [F, Function.comp_def] using
        (eLpNorm_map_measure (p := q) hF.aestronglyMeasurable
          (hX.prodMk hr.1.aemeasurable))
)


end BooleanAnalysis.Hypercontractivity
