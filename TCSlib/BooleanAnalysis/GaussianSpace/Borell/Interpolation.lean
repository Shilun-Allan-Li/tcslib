/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Borell.ProfileCalculus
import TCSlib.BooleanAnalysis.GaussianSpace.Noise

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian stability and the bivariate interpolation functional

## Main definitions

The existing correlated Gaussian measure, stability, and bivariate probability
profile are reused.

## Main results

* `gaussianNoiseStability_le_bivariate_integral`: the bivariate functional
  bounds ordinary Gaussian noise stability.

This is the pointwise comparison step of the Borell semigroup argument.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.3.
* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §§1.6–2.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

local instance {n : ℕ} (ρ : ℝ) :
    IsProbabilityMeasure (correlatedGaussianMeasure (n := n) ρ) := by
  unfold correlatedGaussianMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The bivariate Gaussian profile functional dominates the ordinary stability
of every measurable unit-interval-valued function.
[MN15, §1.6, pointwise comparison with J]

**Proof sketch.** Express stability as an integral over the correlated Gaussian
pair. At each pair the product of the two function values is bounded by the
profile at those values. Both integrands are integrable by boundedness, so
integrating the pointwise inequality proves the claim. -/
theorem gaussianNoiseStability_le_bivariate_integral {n : ℕ}
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (f : (Fin n → ℝ) → ℝ) (hf : Measurable f)
    (hfrange : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    gaussianNoiseStability ρ f ≤
      ∫ z, gaussianBivariateStability ρ (f z.1) (f z.2) ∂correlatedGaussianMeasure ρ := by
  have hc : ρ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2.le⟩
  have hL2 : MemLp f 2 (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    memLp_of_bounded (Filter.Eventually.of_forall hfrange) hf.aestronglyMeasurable 2
  rw [gaussianNoiseStability, ← integral_correlatedGaussianMeasure hc hL2 hL2]
  apply integral_mono (integrable_correlatedGaussianMeasure_mul hc hL2 hL2)
    (integrable_gaussianBivariateStability_comp (correlatedGaussianMeasure ρ) hc
      (hf.comp measurable_fst) (hf.comp measurable_snd)
      (fun z => hfrange z.1) (fun z => hfrange z.2))
  intro z
  exact mul_le_gaussianBivariateStability hρ (hfrange z.1) (hfrange z.2)

end BooleanAnalysis.GaussianSpace
