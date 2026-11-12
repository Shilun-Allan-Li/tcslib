/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Definitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian noise: concrete definitions

## Main definitions

* `correlatedGaussianMeasure`: the law of a correlated pair of Gaussian vectors.
* `gaussianNoise`: the Mehler averaging operator in the correlation parameter.
* `gaussianNoiseStability`: the correlated second moment of a real function.

## Main results

Definitions only. `Noise` supplies the statement layer. Gaussian measures and
the existing indicator-averaging and rotation constructions are reused.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Definitions 11.6, 11.10, 11.12 and 11.18.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- The law of `(g, ρg + sqrt(1-ρ²)g')` for independent standard Gaussian vectors.
It is a correlated standard Gaussian pair when `-1 ≤ ρ ≤ 1`.
[OD14, Defs. 11.6 and 11.10; Fact 11.7]
The pushforward is total; all Gaussian-law assertions restrict the correlation. -/
noncomputable def correlatedGaussianMeasure {n : ℕ} (ρ : ℝ) :
    Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
  ((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
    (Measure.pi fun _ : Fin n => standardGaussianMeasure)).map
      (fun z => (z.1, fun i => ρ * z.1 i + Real.sqrt (1 - ρ ^ 2) * z.2 i))

/-- The Gaussian noise operator averages a function over the second endpoint of
a correlated pair with its first endpoint fixed. [OD14, Def. 11.12]
It uses the existing standard Gaussian law; integrability is required explicitly
by analytic results, since the Bochner integral is totalized. -/
noncomputable def gaussianNoise {n : ℕ} (ρ : ℝ)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y : Fin n → ℝ, f (fun i => ρ * x i + Real.sqrt (1 - ρ ^ 2) * y i)
    ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)

/-- Gaussian noise stability is the expected product at correlated Gaussian
endpoints, expressed using the noise operator. [OD14, Def. 11.18]
The intended domain is Gaussian L² and correlations in `[-1,1]`. -/
noncomputable def gaussianNoiseStability {n : ℕ} (ρ : ℝ)
    (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, f x * gaussianNoise ρ f x
    ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)

end BooleanAnalysis.GaussianSpace
