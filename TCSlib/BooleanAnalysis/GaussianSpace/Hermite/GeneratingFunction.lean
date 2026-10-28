/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The exponential generating function for Hermite polynomials

## Main definitions

The probabilists' Hermite polynomials and their factorial normalization are reused.

## Main results

The scalar Hermite polynomials have exponential generating function
`exp(tx-t²/2)`, with convergence for every real pair of parameters.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.2, Definition 11.29, equation (11.8).
-/

open scoped BigOperators Topology

namespace BooleanAnalysis.GaussianSpace

/-- Differentiating a Hermite-weighted quadratic exponential advances its
Hermite index. [OD14, Def. 11.29, equation (11.8)]

**Proof sketch.** The chain rule differentiates the Hermite argument with a
minus sign and the exponential with the factor `x-z`. Their combination is
exactly the defining Hermite recurrence. -/
private lemma hasDerivAt_hermite_mul_exp_quadratic (k : ℕ) (x z : ℂ) :
    HasDerivAt
      (fun w : ℂ => Polynomial.aeval (x - w) (Polynomial.hermite k) *
        Complex.exp (x * w - w ^ 2 / 2))
      (Polynomial.aeval (x - z) (Polynomial.hermite (k + 1)) *
        Complex.exp (x * z - z ^ 2 / 2)) z := by
  have hq : HasDerivAt (fun w : ℂ => x * w - w ^ 2 / 2) (x - z) z := by
    convert ((hasDerivAt_id z).const_mul x).sub
      (((hasDerivAt_id z).pow 2).div_const 2) using 1
    simp only [id_eq]
    ring
  convert (((Polynomial.hermite k).hasDerivAt_aeval (x - z)).comp z
    ((hasDerivAt_id z).const_sub x)).mul
    ((Complex.hasDerivAt_exp (x * z - z ^ 2 / 2)).comp z hq) using 1
  rw [Polynomial.hermite_succ]
  simp only [map_sub, map_mul, Polynomial.aeval_X, Function.comp_apply]
  ring

/-- Iterated derivatives of a quadratic exponential are its products with the
corresponding shifted Hermite polynomials. [OD14, Def. 11.29, equation (11.8)]

**Proof sketch.** Induct on the derivative order using the single-derivative
Hermite identity. -/
private lemma iteratedDeriv_exp_quadratic (k : ℕ) (x z : ℂ) :
    iteratedDeriv k (fun w : ℂ => Complex.exp (x * w - w ^ 2 / 2)) z =
      Polynomial.aeval (x - z) (Polynomial.hermite k) *
        Complex.exp (x * z - z ^ 2 / 2) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, funext ih]
    exact (hasDerivAt_hermite_mul_exp_quadratic k x z).deriv

/-- Probabilists' Hermite polynomials have exponential generating function
`exp(tx-t²/2)`. This is the source formula with unnormalized polynomials.
[OD14, Def. 11.29, equation (11.8)]

**Proof sketch.** Apply the global Taylor expansion of the entire complex
quadratic exponential at zero. Identify its derivatives with Hermite polynomials,
then restrict the parameters and the resulting series to the reals. -/
theorem hermite_generating_function (x t : ℝ) :
    HasSum (fun j : ℕ => Polynomial.aeval x (Polynomial.hermite j) *
      t ^ j / (j.factorial : ℝ)) (Real.exp (t * x - t ^ 2 / 2)) := by
  apply Complex.hasSum_ofReal.mp
  convert Complex.hasSum_taylorSeries_of_entire
    (f := fun z : ℂ => Complex.exp ((x : ℂ) * z - z ^ 2 / 2))
    (by fun_prop) 0 (t : ℂ) using 1
  · funext j
    simp only [iteratedDeriv_exp_quadratic, sub_zero, mul_zero, smul_eq_mul]
    have hp :
        ((Polynomial.aeval x (Polynomial.hermite j) : ℝ) : ℂ) =
          Polynomial.aeval (x : ℂ) (Polynomial.hermite j) := by
      simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_natCast, hp]
    ring_nf
    simp
  · simp [Complex.ofReal_exp, mul_comm]

/-- A normalized generating-function summand is the corresponding unnormalized
Hermite summand divided by the factorial. [OD14, Def. 11.29, equation (11.8)]

**Proof sketch.** The two normalization factors multiply to the factorial,
which is positive in every degree. -/
private lemma normalizedHermite_generating_summand (j : ℕ) (x t : ℝ) :
    (normalizedHermitePolynomial j).eval x * t ^ j / Real.sqrt (j.factorial : ℝ) =
      Polynomial.aeval x (Polynomial.hermite j) * t ^ j / (j.factorial : ℝ) := by
  simp only [normalizedHermitePolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_map, Polynomial.aeval_def, algebraMap_int_eq]
  rw [inv_mul_eq_div, div_mul_eq_mul_div, div_div, ← pow_two,
    Real.sq_sqrt (Nat.cast_nonneg _)]

/-- The normalized Hermites have the exponential generating function used to
define the source polynomials. [OD14, Def. 11.29, equation (11.8)]
**Proof sketch.** Apply the global Taylor theorem to the quadratic exponential,
whose successive derivatives are Hermite-weighted exponentials. Restrict the
series to real parameters and insert the factorial normalization. -/
theorem normalizedHermite_generating_function (x t : ℝ) :
    HasSum (fun j : ℕ => (normalizedHermitePolynomial j).eval x *
      t ^ j / Real.sqrt (j.factorial : ℝ)) (Real.exp (t * x - t ^ 2 / 2)) := by
  simpa only [normalizedHermite_generating_summand] using hermite_generating_function x t

end BooleanAnalysis.GaussianSpace
