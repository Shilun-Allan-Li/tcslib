/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Localization.ConcaveCompactness
import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.LogConcaveEnvelope
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probability densities from localized concave profiles

## Main definitions

No new definitions.

## Main results

* `integrable_pos_normalized_log_concave_profile_weight`: a bounded
  midpoint-normalized concave profile, multiplied by the exponential of
  a continuous concave exponent, gives a bounded log-concave probability
  density after zero extension and normalization.

## References

* [LS93] László Lovász and Miklós Simonovits, *Random Walks in a Convex Body
  and an Improved Volume Algorithm*, Random Structures & Algorithms 4(4)
  (1993), 359–412, Lemma 2.5, proof of Claim 2, pp.380–381.
* [LV05] László Lovász and Santosh Vempala, *The Geometry of Logconcave
  Functions and Sampling Algorithms*, manuscript revised March 2005, §2.1.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization

/-- A nonnegative concave profile with midpoint value one and values at
most two on the open unit interval gives a bounded log-concave probability
density when raised to a natural power, multiplied by the exponential of
a continuous concave exponent, and normalized.

The unnormalized weight is zero outside the open interval and has a
strictly positive finite integral. Neither endpoint continuity of the
profile nor measurability of its arbitrary values outside the interval
is required. The natural power may be zero; the localization application
uses the positive transverse dimension.

This is normalization and closure glue for the concave-profile stage of
[LS93, Lemma 2.5, Claim 2, pp.380–381], using log-concavity in the
convex-support sense of [LV05, §2.1]. Neither source states this exact
zero-extension interface.

**Proof sketch.** Midpoint positivity and nonnegative concavity imply
strict positivity throughout the open interval. Concavity also makes
the profile continuous there. Bound the exponent on the closed interval,
so the raw weight is bounded on an interval of finite measure; its
restricted continuity gives integrability after zero extension. Its
support is exactly the open unit interval, whose measure is positive,
so its integral is positive. Divide by that integral to obtain unit
mass and preserve nonnegativity and boundedness. Apply the logarithmic
profile-weight closure lemma to the restricted concave exponent to
obtain concavity of the logarithm on the normalized support. -/
theorem integrable_pos_normalized_log_concave_profile_weight
    (φ g : ℝ → ℝ)
    (hφ : ConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) φ)
    (hφmid : φ (1 / 2 : ℝ) = 1)
    (hφbounds : ∀ t ∈ Set.Ioo (0 : ℝ) 1, φ t ∈ Set.Icc (0 : ℝ) 2)
    (hg : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g)
    (hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (m : ℕ) :
    let W : ℝ → ℝ :=
      (Set.Ioo (0 : ℝ) 1).indicator (fun t => (φ t) ^ m * Real.exp (g t))
    let Z : ℝ := ∫ t : ℝ, W t
    let w : ℝ → ℝ := fun t => W t / Z
    Integrable W volume ∧
      0 < Z ∧
      (∀ t : ℝ, 0 ≤ w t) ∧
      BddAbove (Set.range w) ∧
      (∫ t : ℝ, w t) = 1 ∧
      Function.support w = Set.Ioo (0 : ℝ) 1 ∧
      ConcaveOn ℝ (Function.support w) (fun t => Real.log (w t)) :=
  (by
    let W : ℝ → ℝ :=
      (Set.Ioo (0 : ℝ) 1).indicator (fun t => (φ t) ^ m * Real.exp (g t))
    let Z : ℝ := ∫ t : ℝ, W t
    change Integrable W volume ∧ 0 < Z ∧ _
    have hφpos : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 < φ t := by
      have h := pos_on_interior_of_nonneg_concaveOn hφ
        (fun t ht => (hφbounds t ht).1)
        ⟨1 / 2, by constructor <;> norm_num, by rw [hφmid]; norm_num⟩
      simpa only [isOpen_Ioo.interior_eq] using h
    have hWpos (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) : 0 < W t := by
      dsimp only [W]
      rw [Set.indicator_of_mem ht]
      exact mul_pos (pow_pos (hφpos t ht) m) (Real.exp_pos _)
    have hWnonneg : ∀ t, 0 ≤ W t := by
      intro t
      by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
      · exact (hWpos t ht).le
      · dsimp only [W]
        rw [Set.indicator_of_notMem ht]
    have hsupp : Function.support W = Set.Ioo (0 : ℝ) 1 := by
      ext t
      change W t ≠ 0 ↔ t ∈ Set.Ioo (0 : ℝ) 1
      by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
      · exact iff_of_true (hWpos t ht).ne' ht
      · dsimp only [W]
        rw [Set.indicator_of_notMem ht]
        simp only [ne_eq, not_true_eq_false, false_iff]
        exact ht
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (Real.continuous_exp.comp_continuousOn hgcont)
    have hBnonneg : 0 ≤ B := (norm_nonneg (Real.exp (g 0))).trans (hB 0 ⟨le_rfl, by norm_num⟩)
    have hbound : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        ‖(φ t) ^ m * Real.exp (g t)‖ ≤ 2 ^ m * B := by
      intro t ht
      rw [norm_mul, Real.norm_eq_abs, abs_pow, abs_of_nonneg (hφbounds t ht).1]
      exact mul_le_mul (pow_le_pow_left₀ (hφbounds t ht).1 (hφbounds t ht).2 m)
        (hB t ⟨ht.1.le, ht.2.le⟩) (norm_nonneg _) (by positivity)
    have hWint : Integrable W volume := by
      apply IntegrableOn.integrable_indicator (s := Set.Ioo (0 : ℝ) 1) ?_ measurableSet_Ioo
      apply IntegrableOn.of_bound (lt_of_le_of_lt (measure_mono (μ := volume) Set.Ioo_subset_Icc_self)
        isCompact_Icc.measure_lt_top) ?_ (2 ^ m * B) ?_
      · exact (((ConcaveOn.continuousOn isOpen_Ioo hφ).pow m).mul
          ((Real.continuous_exp.comp_continuousOn hgcont).mono Set.Ioo_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioo
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hbound t ht
    have hZ : 0 < Z := by
      apply (integral_pos_iff_support_of_nonneg hWnonneg hWint).mpr
      rw [hsupp, Real.volume_Ioo]
      norm_num
    have hWbound : ∀ t, W t ≤ 2 ^ m * B := by
      intro t
      by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
      · apply (le_abs_self (W t)).trans
        simpa only [W, Set.indicator_of_mem ht, Real.norm_eq_abs] using hbound t ht
      · dsimp only [W]
        rw [Set.indicator_of_notMem ht]
        positivity
    refine ⟨hWint, hZ, fun t => div_nonneg (hWnonneg t) hZ.le,
      ⟨2 ^ m * B / Z, ?_⟩, ?_, ?_, ?_⟩
    · rintro _ ⟨t, rfl⟩
      exact div_le_div_of_nonneg_right (hWbound t) hZ.le
    · rw [integral_div]
      exact div_self hZ.ne'
    · ext t
      change W t / Z ≠ 0 ↔ t ∈ Set.Ioo (0 : ℝ) 1
      constructor
      · intro ht
        exact (Set.ext_iff.mp hsupp t).mp (div_ne_zero_iff.mp ht).1
      · intro ht
        exact div_ne_zero ((Set.ext_iff.mp hsupp t).mpr ht) hZ.ne'
    · have heq : (fun t : ℝ => W t / Z) = (Set.Ioo (0 : ℝ) 1).indicator
          (fun t : ℝ => (φ t) ^ m * Real.exp (g t) / Z) := by
        funext t
        dsimp only [W]
        simp only [div_eq_mul_inv, Set.indicator_mul_const]
      rw [heq]
      exact concaveOn_log_indicator_pow_mul_exp_div (Set.Ioo (0 : ℝ) 1) φ g hφ hφpos
        (hg.subset Set.Ioo_subset_Icc_self (convex_Ioo _ _)) m Z hZ

)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration.Localization
