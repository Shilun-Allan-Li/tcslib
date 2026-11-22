/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.MajorityIsStablest.Clipping
import TCSlib.BooleanAnalysis.GaussianSpace.MajorityIsStablest.Smoothing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The intermediate Majority Is Stablest estimate

## Main definitions

All Boolean and Gaussian functions use their existing representations.

## Main results

* `majority_is_stablest_intermediate`: the sum of the smoothing and clipping errors.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.7, proof of (11.39).
-/

open MeasureTheory ProbabilityTheory
namespace BooleanAnalysis.GaussianSpace.MajorityIsStablest
open ThresholdFunctions Hypercontractivity

/-- Small noisy influences give the general-volume bound with error
`2δ/(1-ρ) + A ε^(δ/6)` for a universal positive A.
[OD14, §11.7, proof of (11.39)]

**Proof sketch.** Extend the smoothed Boolean function to Gaussian space.
Its mean, second moment and stability match. Lipschitz invariance controls its
clipping distance. Borell and stability continuity give the Gaussian profile
bound; the Fourier smoothing estimate returns to the original function. -/
theorem majority_is_stablest_intermediate :
    ∃ A : ℝ, 0 < A ∧ ∀ {n : ℕ} (f : BooleanFunc n),
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 / 20 →
      (∀ i, KKL.noisyInfluence (1 - δ) i f ≤ ε) →
      ∀ ρ : ℝ, ρ ∈ Set.Ioo (0 : ℝ) 1 →
      noiseStability ρ f ≤ gaussianHalfspaceStability ρ (expect f) +
        2 * δ / (1 - ρ) + A * ε ^ (δ / 6) := by
  obtain ⟨K, hK, hclip⟩ := smoothed_clipping_error
  refine ⟨4 * Real.sqrt (2*K), by positivity, ?_⟩
  intro n f hf ε δ hε hε1 hδ hδ20 hinf ρ hρ
  let g := noiseOp (1 - δ) f
  have hg (x : BoolCube n) : g x ∈ Set.Icc (0 : ℝ) 1 :=
    noiseOp_mem_unitInterval f hf ⟨by linarith, by linarith⟩ x
  have hmean : expect g = expect f := by
    rw [← fourierCoeff_empty, noiseOp_fourier]
    simp only [Finset.card_empty, pow_zero, one_mul, fourierCoeff_empty]
  have hmeanQ : (∫ z, evalMultilinearRV (fourierCoeff g) (fun i z => z i) z
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) ∈ Set.Icc (0 : ℝ) 1 := by
    rw [integral_gaussianExtension]
    exact ⟨expect_nonneg (fun x => (hg x).1), by
      simpa using expect_mono (g := fun _ => 1) (fun x => (hg x).2)⟩
  have hb := stability_le_profile_add_clipping_error hρ
    (gaussianExtension_measurable g) (gaussianExtension_memLp g)
    (gaussianExtension_two_norm_le_one g hg) hmeanQ
    (hclip f hf ε δ hε hε1 hδ hδ20 hinf)
  have hc : ρ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2.le⟩
  rw [gaussianNoiseStability_fourier_extension g hc,
    integral_gaussianExtension, hmean] at hb
  have hs := noiseStability_sub_noiseOp_le f hf hρ
    (show δ ∈ Set.Icc (0 : ℝ) 1 from ⟨hδ.le, by linarith⟩)
  change noiseStability ρ f - noiseStability ρ g ≤ _ at hs
  nlinarith only [hb, hs]

end BooleanAnalysis.GaussianSpace.MajorityIsStablest
