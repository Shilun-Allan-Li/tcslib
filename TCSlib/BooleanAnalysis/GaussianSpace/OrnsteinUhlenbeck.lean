/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Noise
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The positive Ornstein–Uhlenbeck generator

## Main definitions

* `HasGaussianGenerator`: the positive generator as a strong Gaussian L² limit.
* `InGaussianGeneratorDomain`: existence of that limit.
* `gaussianOUDifferential`: the ordinary differential expression `x·∇f-Δf`.
* `gaussianEntropy`: entropy relative to the existing product Gaussian law.

## Main results

The differential expression, semigroup differentiation and commutation,
integration by parts and Gaussian log-Sobolev are statement-only obligations.
The generator relation avoids choosing representatives of almost-everywhere
equivalence classes and gives an explicit domain for the source's operator.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Definition 11.24, Remark 11.25,
  Propositions 11.26–11.28, Gaussian Log-Sobolev and Exercise 11.18.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- A function has positive Gaussian generator `g` when `(f-U_(exp(-t))f)/t`
converges to `g` in Gaussian L² as `t` decreases to zero.
[OD14, Def. 11.24; Remark 11.25; Ex. 11.18]
Both representatives belong to L². The positive sign agrees with the number
operator; its Hermite eigenvalues are the nonnegative total degrees. -/
def HasGaussianGenerator {n : ℕ} (f g : (Fin n → ℝ) → ℝ) : Prop :=
  MemLp f 2 (Measure.pi fun _ : Fin n => standardGaussianMeasure) ∧
    MemLp g 2 (Measure.pi fun _ : Fin n => standardGaussianMeasure) ∧
    Tendsto (fun t : ℝ => eLpNorm
      (fun x => (f x - gaussianNoise (Real.exp (-t)) f x) / t - g x)
      2 (Measure.pi fun _ : Fin n => standardGaussianMeasure))
      (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- The strong L² domain of the positive Ornstein–Uhlenbeck generator.
[OD14, Def. 11.24; Ex. 11.18] -/
def InGaussianGeneratorDomain {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ g, HasGaussianGenerator f g

/-- The classical positive Ornstein–Uhlenbeck expression `x·∇f-Δf`, evaluated
using Fréchet derivatives and the standard coordinate vectors.
[OD14, Prop. 11.26] Totalized derivatives are used only under smoothness hypotheses. -/
noncomputable def gaussianOUDifferential {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  (fderiv ℝ f x) x - ∑ i : Fin n,
    (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single i 1)) x) (Pi.single i 1)

/-- Entropy of a nonnegative function under the product standard Gaussian law.
[OD14, §11.1, Gaussian Log-Sobolev]
Analytic results impose the needed sign and integrability conditions explicitly. -/
noncomputable def gaussianEntropy {n : ℕ} (f : (Fin n → ℝ) → ℝ) : ℝ :=
  (∫ x, f x * Real.log (f x) ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) -
    (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) *
      Real.log (∫ x, f x ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure))

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

/-- The strong L² generator is unique up to Gaussian almost-everywhere equality.
[OD14, Def. 11.24] **Proof sketch.** Uniqueness of limits gives zero L² distance
between the two proposed limits, hence almost-everywhere equality. -/
theorem gaussianGenerator_unique {f g h : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) (hfh : HasGaussianGenerator f h) :
    g =ᵐ[γ] h := sorry

/-- On smooth functions in the strong generator domain the generator agrees
almost everywhere with `x·∇f-Δf`. [OD14, Prop. 11.26]

**Proof sketch.** Localize against compactly supported smooth test functions,
Taylor-expand the Gaussian kernel and integrate by parts. The strong L² limit
identifies the resulting differential expression locally, hence almost everywhere. -/
theorem gaussianGenerator_eq_differential {f g : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) (hf : ContDiff ℝ 3 f) :
    g =ᵐ[γ] gaussianOUDifferential f := sorry

/-- Gaussian noise commutes with the strong positive generator.
[OD14, Prop. 11.27] **Proof sketch.** Apply the bounded L² noise operator to the
generator difference quotients and use the semigroup law. -/
theorem gaussianGenerator_noise {f g : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
    HasGaussianGenerator (gaussianNoise ρ f) (gaussianNoise ρ g) := sorry

/-- Differentiating Gaussian noise in its correlation parameter gives the noisy
generator divided by that correlation. [OD14, Prop. 11.27]

**Proof sketch.** Differentiate the semigroup law at its identity in L², then use
the interior Gaussian kernel to obtain pointwise derivatives. -/
theorem hasDerivAt_gaussianNoise {f g : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (hρne : ρ ≠ 0)
    (x : Fin n → ℝ) :
    HasDerivAt (fun r => gaussianNoise r f x) (gaussianNoise ρ g x / ρ) ρ := sorry

/-- In the time parameter, differentiating the noise semigroup gives the
negative noisy positive generator. [OD14, Prop. 11.27]
**Proof sketch.** Apply the correlation derivative identity and the chain rule
to the parameter `exp(-t)`, whose derivative is `-exp(-t)`. -/
theorem hasDerivAt_gaussianNoise_exp {f g : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) (t : ℝ) (ht : 0 < t) (x : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => gaussianNoise (Real.exp (-s)) f x)
      (-gaussianNoise (Real.exp (-t)) g x) t := sorry

/-- The Gaussian generator is symmetric on its strong L² domain.
[OD14, Prop. 11.28] **Proof sketch.** Pair the difference quotients using
self-adjointness of noise, then pass to their L² limits. -/
theorem gaussianGenerator_selfAdjoint {f g u v : (Fin n → ℝ) → ℝ}
    (hfu : HasGaussianGenerator f u) (hgv : HasGaussianGenerator g v) :
    (∫ x, f x * v x ∂γ) = ∫ x, u x * g x ∂γ := sorry

/-- Gaussian integration by parts identifies generator pairing with gradient
energy for smooth functions in its domain. [OD14, Prop. 11.28]

**Proof sketch.** Integrate the Gaussian density derivative in each coordinate;
the drift term cancels the derivative of the density. Approximate in the
generator norm to justify the boundary terms and integrability. -/
theorem gaussianGenerator_integration_by_parts {f g u v : (Fin n → ℝ) → ℝ}
    (hfu : HasGaussianGenerator f u) (hgv : HasGaussianGenerator g v)
    (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) :
    Integrable (fun x => ∑ i : Fin n,
      (fderiv ℝ f x) (Pi.single i 1) * (fderiv ℝ g x) (Pi.single i 1)) γ ∧
      (∫ x, f x * v x ∂γ) = ∫ x, ∑ i : Fin n,
        (fderiv ℝ f x) (Pi.single i 1) * (fderiv ℝ g x) (Pi.single i 1) ∂γ := sorry

/-- Gaussian log-Sobolev bounds entropy of `f²` by twice its generator energy.
[OD14, §11.1, Gaussian Log-Sobolev] The entropy integrability is part of the
conclusion, avoiding a vacuous use of a totalized integral.

**Proof sketch.** Differentiate Gaussian hypercontractivity at exponent two and
correlation one, then extend from smooth approximations in the generator norm. -/
theorem gaussian_logSobolev {f g : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) γ ∧
      gaussianEntropy (fun x => f x ^ 2) ≤ 2 * ∫ x, f x * g x ∂γ := sorry

/-- The smooth form of Gaussian log-Sobolev uses the squared Euclidean gradient.
[OD14, §11.1, Gaussian Log-Sobolev]

**Proof sketch.** Apply generator log-Sobolev and identify its energy through
Gaussian integration by parts with the same smooth function in both slots. -/
theorem gaussian_logSobolev_gradient {f g : (Fin n → ℝ) → ℝ}
    (hfg : HasGaussianGenerator f g) (hf : ContDiff ℝ 3 f) :
    gaussianEntropy (fun x => f x ^ 2) ≤
      2 * ∫ x, ∑ i : Fin n, ((fderiv ℝ f x) (Pi.single i 1)) ^ 2 ∂γ := sorry

end BooleanAnalysis.GaussianSpace
