/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Profile
import TCSlib.BooleanAnalysis.GaussianSpace.IndicatorSmoothing
import Mathlib.Topology.UniformSpace.HeineCantor

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Vanishing profile term for Gaussian indicator approximation

## Main definitions

The existing closed Gaussian profile and averaged Gaussian indicator are reused.

## Main results

* The profile is bounded by an arbitrarily small constant plus a multiple of
  the distance to either endpoint probability.
* The integral profile of an averaged Gaussian indicator tends to zero with
  the averaging angle.

This is the profile part of the smooth-indicator limiting argument. It only
uses measurable sets, Gaussian probability normalization, and the established
integral approximation identity; finite surface area is not required.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Gaussian Isoperimetric Inequality and
  the smooth approximation argument following equation (11.15).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

/-- For any positive error, the closed Gaussian profile on the probability
interval is at most that error plus a fixed positive multiple of the distance
to either endpoint. [OD14, §11.4, smooth indicator approximation argument]

**Proof sketch.** Uniform continuity on the compact probability interval makes
the profile small near either endpoint, where its value is zero. Away from an
endpoint, the distance is bounded below, so a sufficiently large multiple of
that distance dominates a compact uniform bound for the profile. -/
lemma closedGaussianProfile_endpoint_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Icc (0 : ℝ) 1, ∀ b : ℝ,
      (b = 0 ∨ b = 1) → closedGaussianProfile p ≤ ε + C * |p - b| := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuousOn_closedGaussianProfile
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous continuousOn_closedGaussianProfile) ε hε
  refine ⟨max M 1 / δ, div_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hδ, ?_⟩
  intro p hp b hb
  have hbI : b ∈ Icc (0 : ℝ) 1 := by rcases hb with rfl | rfl <;> norm_num
  have hbP : closedGaussianProfile b = 0 := by
    rcases hb with rfl | rfl <;> simp
  by_cases hd : |p - b| < δ
  · have h := hclose p hp b hbI (by simpa only [Real.dist_eq] using hd)
    rw [hbP, Real.dist_eq, sub_zero,
      abs_of_nonneg (closedGaussianProfile_nonneg p)] at h
    exact h.le.trans (le_add_of_nonneg_right (by positivity))
  · have hd' : δ ≤ |p - b| := le_of_not_gt hd
    have hpM : closedGaussianProfile p ≤ max M 1 := by
      have h := hM p hp
      rw [Real.norm_eq_abs] at h
      exact (le_abs_self _).trans (h.trans (le_max_left _ _))
    have hscale : max M 1 ≤ max M 1 / δ * |p - b| := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hδ).mpr (mul_le_mul_of_nonneg_left hd'
        (zero_le_one.trans (le_max_right _ _)))
    exact hpM.trans (hscale.trans (le_add_of_nonneg_left hε.le))

/-- For any positive error, the integral profile of an averaged Gaussian
indicator is at most that error plus a fixed multiple of the rotation
sensitivity. [OD14, §11.4, smooth indicator approximation argument]

**Proof sketch.** Apply the endpoint estimate pointwise, choosing the endpoint
given by the original indicator. Integrate using probability normalization;
the exact indicator-approximation identity identifies the remaining integral
with rotation sensitivity. The integrands are bounded and integrable. -/
lemma integral_profile_averagedGaussianIndicator_le {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ,
      (∫ x : Fin n → ℝ, closedGaussianProfile (averagedGaussianIndicator A θ x)
        ∂(Measure.pi fun _ : Fin n => ThresholdFunctions.standardGaussianMeasure)) ≤
      ε + C * rotationSensitivity A θ := by
  classical
  letI : IsProbabilityMeasure ThresholdFunctions.standardGaussianMeasure := by
    unfold ThresholdFunctions.standardGaussianMeasure
    infer_instance
  obtain ⟨C, hC, hbound⟩ := closedGaussianProfile_endpoint_bound hε
  refine ⟨C, hC, fun θ => ?_⟩
  let μ := Measure.pi fun _ : Fin n => ThresholdFunctions.standardGaussianMeasure
  have hi : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hA
  have herr : Integrable
      (fun x => |averagedGaussianIndicator A θ x - A.indicator (fun _ => (1 : ℝ)) x|) μ :=
    ((integrable_averagedGaussianIndicator hA θ).sub hi).abs
  calc
    _ ≤ ∫ x, (ε + C * |averagedGaussianIndicator A θ x -
        A.indicator (fun _ => (1 : ℝ)) x|) ∂μ := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall fun x => closedGaussianProfile_nonneg _)
        ((integrable_const ε).add (herr.const_mul C))
      filter_upwards [] with x
      apply hbound _ (averagedGaussianIndicator_mem_unitInterval hA θ x)
      by_cases hx : x ∈ A <;> simp [hx]
    _ = ε + C * rotationSensitivity A θ := by
      rw [integral_add (integrable_const ε) (herr.const_mul C), integral_const_mul,
        integral_abs_averagedGaussianIndicator_sub_indicator hA]
      simp [μ]

/-- The integral of the closed Gaussian profile of an averaged measurable
Gaussian indicator tends to zero as the averaging angle tends to zero.
[OD14, §11.4, smooth indicator approximation argument]

**Proof sketch.** The integral is nonnegative. For every positive error it is
bounded by that error plus a constant times rotation sensitivity, which tends
to zero. Taking arbitrarily small errors proves the limit. -/
lemma tendsto_integral_profile_averagedGaussianIndicator {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    Tendsto (fun θ : ℝ => ∫ x : Fin n → ℝ,
      closedGaussianProfile (averagedGaussianIndicator A θ x)
      ∂(Measure.pi fun _ : Fin n => ThresholdFunctions.standardGaussianMeasure))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun θ => ha.trans_le
      (integral_nonneg fun x => closedGaussianProfile_nonneg _)
  · intro b hb
    obtain ⟨C, hC, hbound⟩ := integral_profile_averagedGaussianIndicator_le hA
      (show 0 < b / 2 by linarith)
    have hmajor : Tendsto (fun θ => b / 2 + C * rotationSensitivity A θ)
        (𝓝 (0 : ℝ)) (𝓝 (b / 2)) := by
      simpa using tendsto_const_nhds.add
        (tendsto_const_nhds.mul (rotationSensitivity_tendsto_zero hA))
    filter_upwards [hmajor.eventually (eventually_lt_nhds (show b / 2 < b by linarith))] with θ hθ
    exact (hbound θ).trans_lt hθ

end BooleanAnalysis.GaussianSpace
