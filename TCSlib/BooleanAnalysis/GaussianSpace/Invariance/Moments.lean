/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Inputs
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Coordinates
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Moments
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Polynomial

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial moment bounds for invariance

## Main definitions

The existing polynomial representation and invariance moment hypotheses are reused.

## Main results

* `invariance_polynomial_fourth_moment`: the general-input Bonami bound in coefficients.
* `invariance_coordinate_fourth_moment`: the coordinate derivative bound in terms of influence.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, Corollary 9.6 and §11.6, Hypothesis 11.65.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions Hypercontractivity

/-- A degree-`k` multilinear polynomial in independent inputs satisfying
Hypothesis 11.65 has fourth moment at most `9^k` times the square of its
coefficient second moment. [OD14, Cor. 9.6; §11.6, proof of (11.29)]

**Proof sketch.** Specialize the general-input Bonami inequality to reasonability
constant nine. Orthonormality identifies the polynomial's second moment with
the sum of squared coefficients. -/
theorem invariance_polynomial_fourth_moment
    {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : MultilinearPolynomial n) (hdegree : F.HasDegreeAtMost k)
    (X : Fin n → Ω → ℝ) (hI : iIndepFun X μ)
    (hX : ∀ i, HasInvarianceMoments (X i) μ) :
    (∫ ω, evalMultilinearRV F X ω ^ 4 ∂μ) ≤
      (9 : ℝ) ^ k * (∑ S : Finset (Fin n), F S ^ 2) ^ 2 := by
  have h := (independent_multilinear_reasonable F X 9 (by norm_num) hdegree hI
    (fun i => (hX i).reasonable.memLp) (fun i => (hX i).mean)
    (fun i => (hX i).third) (fun i => (hX i).reasonable)).2.moment_le
  simpa only [max_self, moment, Pi.pow_apply,
    MultilinearMoments.integral_eval_sq F X hI
      (fun i => (hX i).reasonable.memLp) (fun i => (hX i).mean)
      (fun i => (hX i).second)] using h

/-- A coordinate derivative of a degree-`k + 1` polynomial has fourth moment
at most `9^k` times the square of the coordinate influence.
[OD14, §11.6, proof of the Basic Invariance Principle (11.29)]

**Proof sketch.** The derivative has degree at most `k`. Apply general-input
Bonami and identify its coefficient second moment with the influence. -/
theorem invariance_coordinate_fourth_moment
    {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (F : MultilinearPolynomial n) (hdegree : F.HasDegreeAtMost (k + 1))
    (i : Fin n) (X : Fin n → Ω → ℝ) (hI : iIndepFun X μ)
    (hX : ∀ j, HasInvarianceMoments (X j) μ) :
    (∫ ω, evalMultilinearRV (Invariance.coordinateDerivative F i) X ω ^ 4 ∂μ) ≤
      (9 : ℝ) ^ k * (influence i F.eval) ^ 2 := by
  simpa only [Invariance.coordinateDerivative_sum_sq] using
    invariance_polynomial_fourth_moment (Invariance.coordinateDerivative F i)
      (Invariance.coordinateDerivative_degree F i hdegree) X hI hX

end BooleanAnalysis.GaussianSpace
