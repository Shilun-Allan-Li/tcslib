/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.InvarianceExtensions
import Mathlib.Algebra.MvPolynomial.Degrees

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian polynomial anticoncentration and CDF invariance: statement layer

## Main definitions

Arbitrary polynomials use Mathlib's `MvPolynomial`; multilinear Fourier extensions
reuse `fourierCoeff` and `evalMultilinearRV`. Kolmogorov distance is reused.

## Main results

Carbery–Wright and Theorem 11.71, both with universal constants and placeholder proofs.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, Carbery–Wright Theorem and Theorem 11.71.
* [CW01] A. Carbery and J. Wright, Distributional and Lq norm inequalities for
  polynomials over convex bodies in Rn, Mathematical Research Letters 8 (2001),
  233–248, Theorem 8.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions Hypercontractivity

/-- A Gaussian polynomial of second moment one has small-ball probability at
most a universal constant times `k ε^(1/k)`. [OD14, §11.6; CW01, Thm. 8]
The polynomial may contain arbitrary powers, so the existing multilinear type
would be insufficient. Positive degree excludes division by zero in the exponent.

**Proof sketch.** Apply the Carbery–Wright log-concave polynomial inequality to
the standard product Gaussian measure and normalize by the second moment. -/
theorem carbery_wright :
    ∃ K : ℝ, 0 < K ∧ ∀ {n k : ℕ}, 1 ≤ k →
      ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ k →
      (∫ z : Fin n → ℝ, (MvPolynomial.eval z p) ^ 2
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) = 1 →
      ∀ ε : ℝ, 0 < ε →
        ((Measure.pi fun _ : Fin n => standardGaussianMeasure)
          {z | |MvPolynomial.eval z p| ≤ ε}).toReal ≤
          K * (k : ℝ) * ε ^ (1 / (k : ℝ)) := sorry

/-- A variance-one multilinear function with small influences has close Boolean
and Gaussian CDFs, with error `K k ε^(1/(4k+1))`. [OD14, Thm. 11.71]
The variance hypothesis is equality, as in the source.

**Proof sketch.** Compare smoothed half-line tests using fourth-order invariance,
then apply Carbery–Wright to the centered Gaussian polynomial to control the
boundary intervals. Optimize the smoothing width to obtain the exponent. -/
theorem invariance_cdf :
    ∃ K : ℝ, 0 < K ∧ ∀ {n k : ℕ}, 1 ≤ k → ∀ f : BooleanFunc n,
      has_degree_at_most f k → cubeVariance f = 1 →
      ∀ ε : ℝ, 0 ≤ ε → (∀ i, influence i f ≤ ε) →
        kolmogorovDistance
          ((Measure.pi fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure).map f)
          ((Measure.pi fun _ : Fin n => standardGaussianMeasure).map
            (evalMultilinearRV (fourierCoeff f) (fun i z => z i))) ≤
          K * (k : ℝ) * ε ^ (1 / (4 * (k : ℝ) + 1)) := sorry

end BooleanAnalysis.GaussianSpace
