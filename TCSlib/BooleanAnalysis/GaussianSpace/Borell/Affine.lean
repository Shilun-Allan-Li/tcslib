/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Affine changes of Gaussian noise stability

## Main definitions

The Gaussian noise operator and its stability are reused from `Noise`.

## Main results

* `gaussianNoiseStability_affine`: the exact second-moment formula under an affine change.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Definition 11.18.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- An affine change `a * f + b` transforms stability into
`a² * Stab(f) + 2ab * E[f] + b²` for every Gaussian square-integrable input.
[OD14, §11.1, Def. 11.18, affine reformulation]

**Proof sketch.** Linearity of Gaussian averaging gives the affine change of
the conditional mean. Expand the product, integrate its four terms, and use
preservation of the Gaussian mean. Square-integrability supplies all required
integrability bounds. -/
theorem gaussianNoiseStability_affine {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 γ) (a b : ℝ) :
    gaussianNoiseStability ρ (fun x => a * f x + b) =
      a ^ 2 * gaussianNoiseStability ρ f +
        2 * a * b * (∫ x, f x ∂γ) + b ^ 2 := by
  have hi := hf.integrable (by norm_num)
  have hn := gaussianNoise_memLp hρ 2 (by norm_num) hf
  have hni := hn.integrable (by norm_num)
  have hp := hf.integrable_mul hn
  have hnoise : gaussianNoise ρ (fun x => a * f x + b) =
      fun x => a * gaussianNoise ρ f x + b := by
    rw [gaussianNoise_add hρ (hi.const_mul a) (integrable_const b),
      gaussianNoise_const_mul]
    simp [gaussianNoise]
  unfold gaussianNoiseStability
  rw [hnoise]
  calc
    _ = ∫ x, a ^ 2 * (f x * gaussianNoise ρ f x) +
        (a * b) * f x + (a * b) * gaussianNoise ρ f x + b ^ 2 ∂γ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
    _ = _ := by
      rw [integral_add (f := fun x => a ^ 2 * (f x * gaussianNoise ρ f x) +
          (a * b) * f x + (a * b) * gaussianNoise ρ f x) (g := fun _ => b ^ 2)
          (((hp.const_mul (a ^ 2)).add (hi.const_mul (a * b))).add
            (hni.const_mul (a * b))) (integrable_const (b ^ 2)),
        integral_add (f := fun x => a ^ 2 * (f x * gaussianNoise ρ f x) + (a * b) * f x)
          (g := fun x => (a * b) * gaussianNoise ρ f x)
          ((hp.const_mul (a ^ 2)).add (hi.const_mul (a * b))) (hni.const_mul (a * b)),
        integral_add (f := fun x => a ^ 2 * (f x * gaussianNoise ρ f x))
          (g := fun x => (a * b) * f x) (hp.const_mul (a ^ 2)) (hi.const_mul (a * b))]
      simp only [integral_const_mul, integral_const, measureReal_univ_eq_one,
        smul_eq_mul, one_mul, integral_gaussianNoise hρ hi]
      ring

end BooleanAnalysis.GaussianSpace
