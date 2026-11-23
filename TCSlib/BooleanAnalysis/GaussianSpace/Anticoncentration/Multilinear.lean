/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.InputMoments
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Moments
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Basic
import Mathlib.Algebra.MvPolynomial.Degrees

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial representations and Gaussian moments of multilinear extensions

## Main definitions

No new definitions.

## Main results

* `exists_mvPolynomial_eval_eq_evalMultilinearRV`: represent a
  coefficient multilinear extension by an ordinary multivariate
  polynomial without increasing its degree bound.
* `integral_sq_sub_evalMultilinearRV_gaussian_eq_cubeVariance_add_sq`: shifted Gaussian
  second moments equal cube variance plus the squared shifted constant term.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge
  University Press, 2014; May 2021 arXiv edition, §11.6, Definition 11.63
  and proof of Theorem 11.71.
-/

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

open ThresholdFunctions Hypercontractivity
open MeasureTheory ProbabilityTheory

/-- A multilinear extension with coefficient degree at most `k` is the
evaluation of an ordinary real multivariate polynomial of total degree
at most `k`.

This is representation glue between the coefficient model reused by
invariance and the ordinary polynomial model used by Carbery–Wright.
[OD14, §11.6, Definition 11.63 and proof of Theorem 11.71]
It makes no probabilistic assumptions and includes zero variables
and zero degree.

**Proof sketch.** Sum, over all coordinate subsets `S`, the ordinary
monomial `C(F S) * ∏ i∈S, X i`. Evaluation gives exactly the defining
sum for the multilinear extension. A monomial with nonzero coefficient
has degree at most `S.card≤k`; coefficients above level `k`
vanish. Apply the existing total-degree product and finite-sum bounds. -/
theorem exists_mvPolynomial_eval_eq_evalMultilinearRV
    {n k : ℕ} (F : ThresholdFunctions.MultilinearPolynomial n)
    (hdegree : F.HasDegreeAtMost k) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      p.totalDegree ≤ k ∧
        ∀ x : Fin n → ℝ,
          MvPolynomial.eval x p =
            Hypercontractivity.evalMultilinearRV F (fun i z => z i) x :=
  (by
    classical
    refine ⟨∑ S : Finset (Fin n), MvPolynomial.C (F S) * ∏ i ∈ S, MvPolynomial.X i, ?_, ?_⟩
    · apply MvPolynomial.totalDegree_finsetSum_le
      intro S _
      by_cases hS : S.card ≤ k
      · calc
          _ ≤ (MvPolynomial.C (F S) : MvPolynomial (Fin n) ℝ).totalDegree +
              (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          _ ≤ 0 + ∑ i ∈ S, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ).totalDegree :=
            add_le_add (MvPolynomial.totalDegree_C (F S)).le
              (MvPolynomial.totalDegree_finset_prod S _)
          _ ≤ k := by simpa only [MvPolynomial.totalDegree_X, Finset.sum_const,
            smul_eq_mul, mul_one, zero_add] using hS
      · rw [hdegree S (lt_of_not_ge hS), MvPolynomial.C_0, zero_mul, MvPolynomial.totalDegree_zero]
        exact Nat.zero_le k
    · intro x
      change MvPolynomial.eval x _ = ∑ S : Finset (Fin n), F S * ∏ i ∈ S, x i
      simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul,
        MvPolynomial.eval_C, MvPolynomial.eval_prod, MvPolynomial.eval_X]
)

/-- The Gaussian second moment of a multilinear extension shifted by
an arbitrary real constant is its cube variance plus the squared
difference between its constant coefficient and that shift.

This is the orthogonality identity behind the variance normalization in
[OD14, §11.6, Remark 11.64 and proof of Theorem 11.71].
No zero-mean or degree hypothesis is needed.

**Proof sketch.** Standard Gaussian coordinates are independent,
centered, and have unit second moments. Apply the existing multilinear
second-moment identity after subtracting the shift from the constant
coefficient. The nonconstant coefficient squares sum to the existing
cube variance; the remaining square is the shifted constant term. -/
theorem integral_sq_sub_evalMultilinearRV_gaussian_eq_cubeVariance_add_sq
    {n : ℕ} (F : ThresholdFunctions.MultilinearPolynomial n) (u : ℝ) :
    (∫ z : Fin n → ℝ,
      (Hypercontractivity.evalMultilinearRV F (fun i z => z i) z - u) ^ 2
        ∂(Measure.pi fun _ : Fin n => ThresholdFunctions.standardGaussianMeasure)) =
      Hypercontractivity.cubeVariance F.eval + (F ∅ - u) ^ 2 :=
  (by
    classical
    letI : IsProbabilityMeasure standardGaussianMeasure :=
      hasInvarianceMoments_standardGaussian.reasonable.probability
    let G : MultilinearPolynomial n := fun S => F S - if S = ∅ then u else 0
    have heval (z : Fin n → ℝ) :
        evalMultilinearRV G (fun i z => z i) z =
          evalMultilinearRV F (fun i z => z i) z - u := by
      change (∑ S : Finset (Fin n), G S * ∏ i ∈ S, z i) =
        (∑ S : Finset (Fin n), F S * ∏ i ∈ S, z i) - u
      simp only [G, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
        Fintype.sum_ite_eq', Finset.prod_empty, mul_one]
    have hI : iIndepFun (fun (i : Fin n) (z : Fin n → ℝ) => z i)
        (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
      iIndepFun_pi (μ := fun _ : Fin n => standardGaussianMeasure)
        (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
    rw [show (fun z : Fin n → ℝ =>
        (evalMultilinearRV F (fun i z => z i) z - u) ^ 2) =
          (fun z => evalMultilinearRV G (fun i z => z i) z ^ 2) by
        funext z
        rw [heval],
      MultilinearMoments.integral_eval_sq G _ hI
        (fun i => (hasInvarianceMoments_gaussianCoordinate i).reasonable.memLp)
        (fun i => (hasInvarianceMoments_gaussianCoordinate i).mean)
        (fun i => (hasInvarianceMoments_gaussianCoordinate i).second),
      cubeVariance_eq_sum_nonempty_fourier]
    simp_rw [MultilinearPolynomial.fourierCoeff_eval]
    have hterm (S : Finset (Fin n)) : G S ^ 2 =
        (if S = ∅ then 0 else F S ^ 2) +
          (if S = ∅ then (F ∅ - u) ^ 2 else 0) := by
      by_cases hS : S = ∅
      · subst S
        simp only [G, ite_true, zero_add]
      · simp only [G, if_neg hS, sub_zero, add_zero]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']

)


end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
