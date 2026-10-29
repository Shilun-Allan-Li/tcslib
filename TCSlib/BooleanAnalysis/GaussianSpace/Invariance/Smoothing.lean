/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Taylor

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Quantitative smoothing of Lipschitz tests

## Main definitions

* `Invariance.intervalSmooth`: the native interval average of a translated real function.

## Main results

* `Invariance.intervalSmooth_hasDerivAt`: averaging differentiates to an endpoint difference.
* `Invariance.intervalSmooth_iterate_exists_value`: localization of averaged values.
* `Invariance.intervalSmooth_iterate_bounds`: regularity and quantitative bounds for repeated
  averaging.
* `Invariance.exists_contDiff_four_approx`: a Lipschitz test has a quantitative `C⁴`
  approximation.
* `Invariance.lipschitz_expectation_bound_of_fourth_derivative`: smooth-test expectation
  bounds imply Lipschitz-test bounds, with explicit universal constant `16`.

The smoothing argument for [OD14, Cor. 11.68] is implemented by four successive
Mathlib interval averages rather than by convolution with a smooth mollifier.
This gives explicit approximation and fourth-derivative bounds.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, Corollary 11.68 and its proof.
-/

open MeasureTheory
open scoped NNReal

namespace BooleanAnalysis.GaussianSpace.Invariance

/-- The average of a real function over the interval of length `η` starting at `x`.
Four such averages give the quantitative smoothing used in [OD14, Cor. 11.68 (proof)],
with interval averaging replacing the source's convolution mollifier. -/
noncomputable def intervalSmooth (η : ℝ) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨍ t in 0..η, ψ (x + t)

/-- Averaging a continuous function over a translated interval of positive length
gives a differentiable function whose derivative is the normalized endpoint difference.
[OD14, Cor. 11.68 (proof), interval-average adaptation]

**Proof sketch.** Write the average as the difference of the values at `x + η` and
`x` of an integral primitive, divided by `η`. Apply the fundamental theorem of calculus
to both terms. -/
theorem intervalSmooth_hasDerivAt {η : ℝ} (_hη : 0 < η)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (x : ℝ) :
    HasDerivAt (intervalSmooth η ψ) ((ψ (x + η) - ψ x) / η) x := by
  have hprimitive (u : ℝ) :
      HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, ψ t) (ψ u) u :=
    intervalIntegral.integral_hasDerivAt_right (hψ.intervalIntegrable _ _)
      hψ.aestronglyMeasurable.stronglyMeasurableAtFilter hψ.continuousAt
  have havg : intervalSmooth η ψ =
      fun y => ((∫ t in (0 : ℝ)..y + η, ψ t) - ∫ t in (0 : ℝ)..y, ψ t) / η := by
    funext y
    rw [intervalSmooth, interval_average_eq_div,
      intervalIntegral.integral_comp_add_left, add_zero, sub_zero,
      intervalIntegral.integral_interval_sub_left
        (hψ.intervalIntegrable _ _) (hψ.intervalIntegrable _ _)]
  rw [havg]
  exact ((hprimitive (x + η)).comp_add_const x η |>.sub (hprimitive x)).div_const η

/-- Averaging a real `C^m` function over a positive interval gives a `C^(m+1)` function.
[OD14, Cor. 11.68 (proof), interval-average adaptation]

**Proof sketch.** The derivative of the average is a normalized difference of two
translates of the original function. This derivative is `C^m`. -/
theorem contDiff_intervalSmooth {η : ℝ} (hη : 0 < η) {ψ : ℝ → ℝ}
    (m : ℕ) (hψ : ContDiff ℝ m ψ) :
    ContDiff ℝ (m + 1 : ℕ) (intervalSmooth η ψ) := by
  rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by simp,
    contDiff_succ_iff_deriv]
  refine ⟨fun x => (intervalSmooth_hasDerivAt hη hψ.continuous x).differentiableAt,
    by simp, ?_⟩
  have hderiv : deriv (intervalSmooth η ψ) =
      fun x => (ψ (x + η) - ψ x) / η :=
    funext fun x => (intervalSmooth_hasDerivAt hη hψ.continuous x).deriv
  rw [hderiv]
  exact ((hψ.comp (contDiff_id.add contDiff_const)).sub hψ).div_const η

/-- Any finite number of positive-width interval averages preserves continuity.
This is technical regularity glue for smooth cutoffs. -/
theorem continuous_intervalSmooth_iterate {η : ℝ} (hη : 0 < η)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (m : ℕ) :
    Continuous (((intervalSmooth η)^[m]) ψ) := by
  induction m with
  | zero => simpa using hψ
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (contDiff_intervalSmooth hη 0 (contDiff_zero.mpr ih)).continuous

/-- Repeated interval averaging of a continuous real function equals one of
its values within the interval covered by the averaging steps.
[OD14, Cor. 11.70 (proof), interval-average adaptation]

**Proof sketch.** Each average equals a value at an interior point by the mean
value theorem for integrals. Inductively combine the positions of these points. -/
theorem intervalSmooth_iterate_exists_value
    {η : ℝ} (hη : 0 < η) {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (m : ℕ) (x : ℝ) :
    ∃ y ∈ Set.Icc x (x + (m : ℝ) * η), (((intervalSmooth η)^[m]) ψ) x = ψ y := by
  induction m generalizing x with
  | zero => exact ⟨x, by simp, by simp⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨t, ht, he⟩ := exists_eq_interval_average
      (f := fun s => (((intervalSmooth η)^[m]) ψ) (x + s)) (ne_of_lt hη)
      ((continuous_intervalSmooth_iterate hη hψ m).comp
        (continuous_const.add continuous_id)).continuousOn
    rw [Set.uIoo_of_lt hη] at ht
    obtain ⟨y, hy, hval⟩ := ih (x + t)
    refine ⟨y, ⟨by linarith [hy.1, ht.1], ?_⟩, ?_⟩
    · push_cast
      nlinarith [hy.2, ht.2]
    · change (⨍ s in 0..η, (((intervalSmooth η)^[m]) ψ) (x + s)) = ψ y
      rw [← he, hval]

/-- The `(m+1)`st derivative of an interval average is the normalized difference of
the `m`th derivatives at its endpoints.
[OD14, Cor. 11.68 (proof), interval-average adaptation]

**Proof sketch.** Differentiate the average once by the fundamental theorem of calculus,
then differentiate the two endpoint translates `m` times. -/
theorem iteratedDeriv_intervalSmooth {η : ℝ} (hη : 0 < η) {ψ : ℝ → ℝ}
    (m : ℕ) (hψ : ContDiff ℝ m ψ) (x : ℝ) :
    iteratedDeriv (m + 1) (intervalSmooth η ψ) x =
      (iteratedDeriv m ψ (x + η) - iteratedDeriv m ψ x) / η := by
  have hshift : ContDiff ℝ m (fun y => ψ (y + η)) :=
    hψ.comp (contDiff_id.add contDiff_const)
  have hderiv : deriv (intervalSmooth η ψ) =
      fun y => η⁻¹ * (ψ (y + η) - ψ y) := by
    funext y
    rw [(intervalSmooth_hasDerivAt hη hψ.continuous y).deriv]
    ring
  rw [iteratedDeriv_succ', hderiv,
    iteratedDeriv_const_mul ((hshift.sub hψ).contDiffAt) η⁻¹]
  rw [show (fun y => ψ (y + η) - ψ y) = (fun y => ψ (y + η)) - ψ by rfl,
    iteratedDeriv_sub hshift.contDiffAt hψ.contDiffAt,
    iteratedDeriv_comp_add_const]
  simp only [div_eq_mul_inv, mul_comm]

/-- The derivative of an interval average of a `c`-Lipschitz function is bounded by `c`.
[OD14, Cor. 11.68 (proof), interval-average adaptation] -/
theorem abs_deriv_intervalSmooth_le {η : ℝ} (hη : 0 < η) {c : ℝ≥0}
    {ψ : ℝ → ℝ} (hψ : LipschitzWith c ψ) (x : ℝ) :
    |deriv (intervalSmooth η ψ) x| ≤ (c : ℝ) := by
  rw [(intervalSmooth_hasDerivAt hη hψ.continuous x).deriv,
    abs_div, abs_of_pos hη, div_le_iff₀ hη]
  simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_pos hη] using
    hψ.dist_le_mul (x + η) x

/-- Averaging a `c`-Lipschitz real function over a fixed positive interval preserves
its Lipschitz constant. [OD14, Cor. 11.68 (proof), interval-average adaptation]

**Proof sketch.** The average is differentiable, with derivative bounded by `c`.
Apply the mean value theorem. -/
theorem lipschitz_intervalSmooth {η : ℝ} (hη : 0 < η) {c : ℝ≥0}
    {ψ : ℝ → ℝ} (hψ : LipschitzWith c ψ) :
    LipschitzWith c (intervalSmooth η ψ) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (intervalSmooth_hasDerivAt hη hψ.continuous x).differentiableAt)
  intro x
  exact_mod_cast (show ‖deriv (intervalSmooth η ψ) x‖ ≤ (c : ℝ) by
    simpa only [Real.norm_eq_abs] using abs_deriv_intervalSmooth_le hη hψ x)

/-- A positive-width interval average approximates a `c`-Lipschitz function uniformly
within `c` times the width. [OD14, Cor. 11.68 (proof), interval-average adaptation]

**Proof sketch.** The mean value theorem for interval averages realizes the average
as one value of the function inside the interval. Apply the Lipschitz bound there. -/
theorem abs_intervalSmooth_sub_le {η : ℝ} (hη : 0 < η) {c : ℝ≥0}
    {ψ : ℝ → ℝ} (hψ : LipschitzWith c ψ) (x : ℝ) :
    |intervalSmooth η ψ x - ψ x| ≤ (c : ℝ) * η := by
  obtain ⟨t, ht, havg⟩ := exists_eq_interval_average
    (f := fun s => ψ (x + s)) (ne_of_lt hη)
    (hψ.continuous.comp (continuous_const.add continuous_id)).continuousOn
  rw [Set.uIoo_of_lt hη] at ht
  change |(⨍ s in 0..η, ψ (x + s)) - ψ x| ≤ (c : ℝ) * η
  rw [← havg]
  calc
    |ψ (x + t) - ψ x| ≤ (c : ℝ) * t := by
      simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_pos ht.1] using
        hψ.dist_le_mul (x + t) x
    _ ≤ (c : ℝ) * η := mul_le_mul_of_nonneg_left ht.2.le c.coe_nonneg

/-- After `m+1` interval averages, a `c`-Lipschitz function is `C^(m+1)`, remains
`c`-Lipschitz, has approximation error at most `(m+1)cη`, and has highest derivative
bounded by `c(2/η)^m`. [OD14, Cor. 11.68 (proof), interval-average adaptation]

**Proof sketch.** One average has derivative bounded by `c`. Each further average
adds one derivative and at most `cη` to the approximation error. Its highest derivative
is the normalized endpoint difference of the preceding highest derivative, multiplying
the bound by `2/η`. -/
theorem intervalSmooth_iterate_bounds {η : ℝ} (hη : 0 < η) {c : ℝ≥0}
    {ψ : ℝ → ℝ} (hψ : LipschitzWith c ψ) (m : ℕ) :
    let φ := ((intervalSmooth η)^[m + 1]) ψ
    ContDiff ℝ (m + 1 : ℕ) φ ∧ LipschitzWith c φ ∧
      (∀ x, |φ x - ψ x| ≤ ((m + 1 : ℕ) : ℝ) * (c : ℝ) * η) ∧
      ∀ x, |iteratedDeriv (m + 1) φ x| ≤ (c : ℝ) * (2 / η) ^ m := by
  induction m with
  | zero =>
    simp only [zero_add, Function.iterate_one, Nat.cast_one, pow_zero, mul_one, one_mul]
    exact ⟨contDiff_intervalSmooth hη 0 (contDiff_zero.mpr hψ.continuous),
      lipschitz_intervalSmooth hη hψ, abs_intervalSmooth_sub_le hη hψ,
      fun x => by simpa only [iteratedDeriv_one] using abs_deriv_intervalSmooth_le hη hψ x⟩
  | succ m ih =>
    dsimp only at ih ⊢
    rw [Function.iterate_succ_apply' (intervalSmooth η) (m + 1) ψ]
    rcases ih with ⟨hsmooth, hlip, happ, hbound⟩
    refine ⟨contDiff_intervalSmooth hη (m + 1) hsmooth,
      lipschitz_intervalSmooth hη hlip, ?_, ?_⟩
    · intro x
      have ha := abs_intervalSmooth_sub_le hη hlip x
      have hb := happ x
      have ht := abs_sub_le (intervalSmooth η (((intervalSmooth η)^[m + 1]) ψ) x)
        ((((intervalSmooth η)^[m + 1]) ψ) x) (ψ x)
      push_cast at hb ⊢
      nlinarith
    · intro x
      rw [iteratedDeriv_intervalSmooth hη (m + 1) hsmooth x, abs_div, abs_of_pos hη,
        div_le_iff₀ hη, pow_succ]
      have hb := abs_sub (iteratedDeriv (m + 1) (((intervalSmooth η)^[m + 1]) ψ) (x + η))
        (iteratedDeriv (m + 1) (((intervalSmooth η)^[m + 1]) ψ) x)
      have h1 := hbound (x + η)
      have h2 := hbound x
      field_simp [ne_of_gt hη]
      nlinarith

/-- A `c`-Lipschitz test has a `C⁴` approximation with uniform error at most `4cη`
and fourth derivative at most `8c/η³`. [OD14, Cor. 11.68 (proof)]
The explicit constants here come from four successive Mathlib interval averages
rather than the source's convolution mollifier.

**Proof sketch.** Apply the interval-average iteration bounds with four averages. -/
theorem exists_contDiff_four_approx {η : ℝ} (hη : 0 < η) {c : ℝ≥0}
    {ψ : ℝ → ℝ} (hψ : LipschitzWith c ψ) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 4 φ ∧
      (∀ x, |φ x - ψ x| ≤ 4 * (c : ℝ) * η) ∧
      ∀ x, |iteratedDeriv 4 φ x| ≤ 8 * (c : ℝ) / η ^ 3 := by
  rcases intervalSmooth_iterate_bounds hη hψ 3 with ⟨hC, _, happ, hD⟩
  refine ⟨((intervalSmooth η)^[4]) ψ, hC, ?_, ?_⟩
  · simpa only [Nat.reduceAdd, Nat.cast_ofNat] using happ
  · intro x
    calc
      |iteratedDeriv 4 (((intervalSmooth η)^[4]) ψ) x| ≤ (c : ℝ) * (2 / η) ^ 3 := hD x
      _ = 8 * (c : ℝ) / η ^ 3 := by ring

/-- Uniformly close functions have uniformly close expectations when one is integrable
and the other is almost everywhere strongly measurable. -/
private theorem abs_integral_sub_le_uniform
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : AEStronglyMeasurable g μ)
    {D : ℝ} (hfg : ∀ ω, |f ω - g ω| ≤ D) :
    |(∫ ω, f ω ∂μ) - ∫ ω, g ω ∂μ| ≤ D := by
  have hnorm : ∀ᵐ ω ∂μ, ‖f ω - g ω‖ ≤ D :=
    Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hfg ω
  have hgint : Integrable g μ :=
    integrable_of_norm_sub_le hg hf (integrable_const D) hnorm
  rw [← integral_sub hf hgint]
  simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const hnorm

/-- A fourth-derivative expectation comparison gives a Lipschitz-test comparison
at every positive smoothing scale. [OD14, Cor. 11.68 (proof)]
The constants use four interval averages in place of the source's mollifier.

**Proof sketch.** Approximate the test uniformly within `4cη` by a `C⁴` function
whose fourth derivative is at most `8c/η³`. The two expectation approximation errors
total at most `8cη`; apply the assumed comparison to the smooth function between them.
Finite fourth moments ensure that all these expectations are integrable. -/
private theorem lipschitz_expectation_bound_at_scale
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {U : Ω → ℝ} {V : Ξ → ℝ} (hU : MemLp U 4 μ) (hV : MemLp V 4 ν)
    (B : ℝ) (_hB : 0 ≤ B)
    (herror : ∀ (φ : ℝ → ℝ), ContDiff ℝ 4 φ →
      ∀ C : ℝ, 0 ≤ C → (∀ t, |iteratedDeriv 4 φ t| ≤ C) →
        |(∫ ω, φ (U ω) ∂μ) - (∫ ω, φ (V ω) ∂ν)| ≤ C * B)
    (c : ℝ≥0) (ψ : ℝ → ℝ) (hψ : LipschitzWith c ψ)
    (η : ℝ) (hη : 0 < η) :
    |(∫ ω, ψ (U ω) ∂μ) - (∫ ω, ψ (V ω) ∂ν)| ≤
      8 * (c : ℝ) * η + (8 * (c : ℝ) / η ^ 3) * B := by
  obtain ⟨φ, hφ, happ, hD⟩ := exists_contDiff_four_approx hη hψ
  have hC : 0 ≤ 8 * (c : ℝ) / η ^ 3 := by positivity
  have hleft := abs_integral_sub_le_uniform
    (integrable_test_of_memLp_four hU φ hφ _ hC hD)
    (hψ.continuous.comp_aestronglyMeasurable hU.aestronglyMeasurable)
    (fun ω => happ (U ω))
  have hright := abs_integral_sub_le_uniform
    (integrable_test_of_memLp_four hV φ hφ _ hC hD)
    (hψ.continuous.comp_aestronglyMeasurable hV.aestronglyMeasurable)
    (fun ω => happ (V ω))
  calc
    _ ≤ |(∫ ω, ψ (U ω) ∂μ) - ∫ ω, φ (U ω) ∂μ| +
        (|(∫ ω, φ (U ω) ∂μ) - ∫ ω, φ (V ω) ∂ν| +
          |(∫ ω, φ (V ω) ∂ν) - ∫ ω, ψ (V ω) ∂ν|) :=
      (abs_sub_le _ _ _).trans (add_le_add_left (abs_sub_le _ _ _) _)
    _ ≤ 4 * (c : ℝ) * η + ((8 * (c : ℝ) / η ^ 3) * B + 4 * (c : ℝ) * η) :=
      add_le_add (by simpa only [abs_sub_comm] using hleft)
        (add_le_add (herror φ hφ _ hC hD) hright)
    _ = _ := by ring

/-- A fourth-derivative expectation comparison with coefficient `B` implies an
expectation error at most `16 c B^(1/4)` for every `c`-Lipschitz test.
[OD14, Cor. 11.68 (proof)]
The explicit constant `16` comes from four successive Mathlib interval averages.

**Proof sketch.** Smoothing at scale `η` gives error at most `8cη + 8cB/η³`.
For positive `B`, choose `η = B^(1/4)`. For `B = 0`, let the scale decrease to zero.
Finite fourth moments ensure all the test expectations exist. -/
theorem lipschitz_expectation_bound_of_fourth_derivative
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {U : Ω → ℝ} {V : Ξ → ℝ} (hU : MemLp U 4 μ) (hV : MemLp V 4 ν)
    (B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ (φ : ℝ → ℝ), ContDiff ℝ 4 φ →
      ∀ C : ℝ, 0 ≤ C → (∀ t, |iteratedDeriv 4 φ t| ≤ C) →
        |(∫ ω, φ (U ω) ∂μ) - (∫ ω, φ (V ω) ∂ν)| ≤ C * B)
    (c : ℝ≥0) (ψ : ℝ → ℝ) (hψ : LipschitzWith c ψ) :
    |(∫ ω, ψ (U ω) ∂μ) - (∫ ω, ψ (V ω) ∂ν)| ≤
      16 * (c : ℝ) * B ^ (1 / 4 : ℝ) := by
  rcases eq_or_lt_of_le hB with rfl | hBpos
  · simp only [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), mul_zero]
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hden : 0 < 8 * (c : ℝ) + 1 := by positivity
    have hη : 0 < δ / (8 * (c : ℝ) + 1) := div_pos hδ hden
    have h := lipschitz_expectation_bound_at_scale hU hV 0 le_rfl herror c ψ hψ _ hη
    simp only [mul_zero, add_zero] at h
    have heq := div_mul_cancel₀ δ hden.ne'
    nlinarith
  · let η := B ^ (1 / 4 : ℝ)
    have hη : 0 < η := Real.rpow_pos_of_pos hBpos _
    have hpow : η ^ 4 = B := by
      dsimp [η]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
      norm_num
    calc
      _ ≤ 8 * (c : ℝ) * η + (8 * (c : ℝ) / η ^ 3) * B :=
        lipschitz_expectation_bound_at_scale hU hV B hB herror c ψ hψ η hη
      _ = 16 * (c : ℝ) * B ^ (1 / 4 : ℝ) := by
        change 8 * (c : ℝ) * η + (8 * (c : ℝ) / η ^ 3) * B = 16 * (c : ℝ) * η
        rw [← hpow]
        field_simp
        ring

end BooleanAnalysis.GaussianSpace.Invariance
