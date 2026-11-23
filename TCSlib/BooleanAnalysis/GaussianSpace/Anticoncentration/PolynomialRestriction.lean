/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Restricting multivariate polynomials to affine lines

## Main definitions

No new definitions.

## Main results

* `exists_polynomial_eval_lineMap_natDegree_le`: evaluation of a
  multivariate polynomial on an affine line is a univariate polynomial
  of natural degree at most the original total degree.

## References

* [CW01] A. Carbery and J. Wright, *Distributional and Lq norm inequalities
  for polynomials over convex bodies in Rn*, Mathematical Research Letters
  8 (2001), 233–248, §4. The result below isolates the elementary
  degree-preserving line restriction used with localization.
-/

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

/-- Restricting a multivariate polynomial over a commutative ring to
an affine line gives a univariate polynomial whose natural degree is
at most the multivariate polynomial's total degree.

This is the elementary restriction prerequisite for the polynomial
localization argument in [CW01, §4], stated for arbitrary variable
types and commutative coefficient rings. The endpoints may agree.

**Proof sketch.** Substitute the affine univariate polynomial
`C(a i) + C(b i - a i) * X` for each variable. Each substitution
has degree at most one. Expand evaluation as the finite sum over the
original polynomial's supported monomials. Each evaluated monomial
has degree at most the sum of its exponents, which is bounded by
the original total degree. Finite sums preserve that upper bound.
The existing polynomial-valued evaluation identity shows that
evaluation of the resulting polynomial at `t` equals evaluation
of the original polynomial at the affine line point. -/
theorem exists_polynomial_eval_lineMap_natDegree_le
    {σ R : Type*} [CommRing R]
    (p : MvPolynomial σ R) (a b : σ → R) :
    ∃ q : Polynomial R, q.natDegree ≤ p.totalDegree ∧
      ∀ t : R, q.eval t = MvPolynomial.eval (AffineMap.lineMap a b t) p :=
  (by
  classical
  let L (i : σ) : Polynomial R := Polynomial.C (a i) + Polynomial.C (b i - a i) * Polynomial.X
  have hL (i : σ) : (L i).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp only [Polynomial.natDegree_C]; omega
    · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  refine ⟨MvPolynomial.eval₂ Polynomial.C L p, ?_, ?_⟩
  · rw [MvPolynomial.eval₂_eq]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro s hs
    apply Polynomial.natDegree_mul_le.trans
    rw [Polynomial.natDegree_C, zero_add]
    apply (Polynomial.natDegree_prod_le _ _).trans
    calc
      _ ≤ ∑ i ∈ s.support, s i := Finset.sum_le_sum (fun i _ => by
        simpa only [mul_one] using Polynomial.natDegree_pow_le_of_le (s i) (hL i))
      _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hs
  · intro t
    rw [MvPolynomial.polynomial_eval_eval₂]
    change MvPolynomial.eval₂ ((Polynomial.evalRingHom t).comp Polynomial.C)
      (fun i => Polynomial.eval t (L i)) p =
      MvPolynomial.eval₂ (RingHom.id R) (AffineMap.lineMap a b t) p
    congr 1
    · ext r
      simp
    · funext i
      simp only [L, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_X, AffineMap.pi_lineMap_apply, AffineMap.lineMap_apply_module', smul_eq_mul]
      ring
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
