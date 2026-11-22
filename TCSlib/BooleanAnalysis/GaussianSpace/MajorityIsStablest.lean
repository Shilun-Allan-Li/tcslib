/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.MajorityIsStablest.Estimate
import TCSlib.BooleanAnalysis.GaussianSpace.MajorityIsStablest.Parameters

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Quantitative general-volume Majority Is Stablest

## Contents

* `Bridge`: matching Boolean and Gaussian multilinear moments and stability.
* `Perturbation`: L² continuity of Gaussian noise stability.
* `Clipping`: squared-clipping invariance and Borell comparison.
* `Smoothing`: Fourier control of the Boolean smoothing cost.
* `Estimate`: the intermediate smoothing and invariance error bound.
* `Parameters`: the logarithmic choice of smoothing parameter.

## Main definitions

Boolean noise stability, maximum influence and noisy influence use their existing
definitions. The extremal Gaussian profile is defined in `Borell`.

## Main results

Equation (11.39), including the source's no-notables hypothesis and a universal
constant independent of correlation. The balanced qualitative theorem already
exists in `ThresholdFunctions.Gaussian` and is not restated here.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.7, General-Volume Majority Is Stablest, (11.39).
-/

open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- General-volume Majority Is Stablest has error
`C log(log(1/ε))/((1-ρ) log(1/ε))` for functions with no notable coordinates.
[OD14, §11.7, equation (11.39)] The bound `ε ≤ exp(-2)` specifies the source's
small-ε asymptotic regime, keeping the logarithmic error bounded away from its spurious zero at ε = exp(-1).
The constant is universal, in particular independent of `ρ`.

**Proof sketch.** Smooth the Boolean function, use no-notables invariance with
the squared-clipping test to clip its Gaussian extension, and compare the
two stabilities. Apply Borell to the clipped extension. Balance smoothing and
invariance errors at the logarithmic scale stated in the source. -/
theorem majority_is_stablest_general_volume :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (f : BooleanFunc n),
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) → ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-2) →
      (∀ i, KKL.noisyInfluence (1 - 1 / Real.log (1 / ε)) i f ≤ ε) →
      ∀ ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 →
        noiseStability ρ f ≤ gaussianHalfspaceStability ρ (expect f) +
          C * Real.log (Real.log (1 / ε)) / ((1 - ρ) * Real.log (1 / ε)) := by
  obtain ⟨A, hA, hestimate⟩ := MajorityIsStablest.majority_is_stablest_intermediate
  obtain ⟨C, hC, hparameters⟩ := MajorityIsStablest.scalar_parameters A hA.le
  refine ⟨C, hC, ?_⟩
  intro n f hf ε hε hεsmall hinf ρ hρ
  have hlog : 2 ≤ Real.log (1 / ε) := by
    have h := (Real.log_le_iff_le_exp hε).2 hεsmall
    simpa only [one_div, Real.log_inv] using
      (show 2 ≤ -Real.log ε by linarith)
  have hε1 : ε ≤ 1 := hεsmall.trans (Real.exp_le_one_iff.mpr (by norm_num))
  obtain htrivial | ⟨δ, hδlo, hδ, hδ20, herror⟩ :=
    hparameters ε (Real.log (1 / ε)) ρ hε hlog
      (by simp only [one_div, Real.log_inv, neg_neg]) hρ
  · have hs := MajorityIsStablest.noiseStability_le_one f hf ⟨hρ.1.le, hρ.2.le⟩
    have hp : 0 ≤ gaussianHalfspaceStability ρ (expect f) := by
      rw [← gaussianBivariateStability_diag]
      exact (gaussianBivariateStability_mem_unitInterval _ _ _).1
    linarith
  · have hnoisy (i : Fin n) : KKL.noisyInfluence (1 - δ) i f ≤ ε :=
      (MajorityIsStablest.noisyInfluence_mono f i
        (by linarith : 0 ≤ 1 - δ) (by linarith)).trans (hinf i)
    have hs := hestimate f hf ε δ hε hε1 hδ hδ20 hnoisy ρ hρ
    linarith

/-- The same quantitative general-volume bound holds under ordinary small
influences. [OD14, §11.7, equation (11.39), first hypothesis]
This is the source's quantitative unit-interval theorem, distinct from the
existing qualitative balanced `[-1,1]` theorem.

**Proof sketch.** Ordinary influence dominates noisy influence at the required
parameter. Apply the no-notables form with the same universal constant. -/
theorem majority_is_stablest_general_volume_maxInfluence :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (f : BooleanFunc n),
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) → ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-2) →
      maxInfluence f ≤ ε → ∀ ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 →
        noiseStability ρ f ≤ gaussianHalfspaceStability ρ (expect f) +
          C * Real.log (Real.log (1 / ε)) / ((1 - ρ) * Real.log (1 / ε)) := by
  obtain ⟨C, hC, hbound⟩ := majority_is_stablest_general_volume
  refine ⟨C, hC, ?_⟩
  intro n f hf ε hε hεsmall hmax ρ hρ
  have hlog : 2 ≤ Real.log (1 / ε) := by
    have h := (Real.log_le_iff_le_exp hε).2 hεsmall
    simpa only [one_div, Real.log_inv] using
      (show 2 ≤ -Real.log ε by linarith)
  apply hbound f hf ε hε hεsmall ?_ ρ hρ
  intro i
  calc
    KKL.noisyInfluence (1 - 1 / Real.log (1 / ε)) i f ≤ influence i f :=
      KKL.noisyInfluence_le_influence i f _
        (sub_nonneg.mpr ((div_le_one (by linarith : 0 < Real.log (1 / ε))).2
          (by linarith)))
        (sub_le_self _ (one_div_nonneg.mpr (by linarith)))
    _ ≤ |influence i f| := le_abs_self _
    _ ≤ maxInfluence f :=
      le_csSup (Set.finite_range _).bddAbove (Set.mem_range_self i)
    _ ≤ ε := hmax

end BooleanAnalysis.GaussianSpace
