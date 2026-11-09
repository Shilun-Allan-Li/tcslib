/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Hermite.Basic
import TCSlib.BooleanAnalysis.GaussianSpace.Noise.Polynomial
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian integration by parts and Hermite orthogonality

## Main definitions

The standard Gaussian measure and Mathlib's probabilists' Hermite polynomials
are reused.

## Main results

* `integral_polynomial_derivative_standardGaussian`: polynomial Gaussian integration by parts.
* `integral_hermite_mul_polynomial_standardGaussian`: the iterated adjoint identity.
* `integral_normalizedHermite_mul_standardGaussian`: scalar orthonormality.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.2, Proposition 11.30.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- Every real polynomial is integrable against the standard Gaussian measure.
[OD14, §11.1, preceding Thm. 11.22]

**Proof sketch.** Regard the polynomial as a polynomial in one coordinate.
Transfer its Gaussian integrability along the measure-preserving coordinate projection. -/
lemma integrable_polynomial_eval_standardGaussian (p : Polynomial ℝ) :
    Integrable (fun x : ℝ => p.eval x) standardGaussianMeasure := by
  rw [← (measurePreserving_eval (μ := fun _ : Fin 1 => standardGaussianMeasure) 0).integrable_comp
    p.continuous.aestronglyMeasurable]
  simpa only [Function.comp_def, MvPolynomial.eval_toMvPolynomial] using
    (memLp_one_iff_integrable.mp
      (memLp_eval_gaussian (p.toMvPolynomial (0 : Fin 1)) (p := 1) (by norm_num)))

/-- A polynomial multiplied by the standard Gaussian density is Lebesgue integrable.
**Proof sketch.** Write the Gaussian law as a measure with density and transfer
polynomial integrability to Lebesgue measure. -/
private lemma integrable_standardGaussianPDF_mul_polynomial (p : Polynomial ℝ) :
    Integrable (fun x : ℝ => standardGaussianPDF x * p.eval x) := by
  have h := integrable_polynomial_eval_standardGaussian p
  rw [standardGaussianMeasure, gaussianReal_of_var_ne_zero 0 one_ne_zero] at h
  simpa only [toReal_gaussianPDF, smul_eq_mul, standardGaussianPDF] using
    (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)).mp h

/-- Gaussian integration by parts identifies the expected derivative of a polynomial
with the expectation of its product with the coordinate.
[OD14, §11.2, proof of Prop. 11.30]

**Proof sketch.** Differentiate the polynomial multiplied by the Gaussian density.
Both that function and its derivative are integrable, so the derivative integrates to zero. -/
lemma integral_polynomial_derivative_standardGaussian (p : Polynomial ℝ) :
    (∫ x : ℝ, p.derivative.eval x ∂standardGaussianMeasure) =
      ∫ x : ℝ, x * p.eval x ∂standardGaussianMeasure := by
  have hxp : Integrable (fun x => standardGaussianPDF x * (x * p.eval x)) := by
    convert integrable_standardGaussianPDF_mul_polynomial (Polynomial.X * p) using 1
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
  have hzero : (∫ x, standardGaussianPDF x * p.derivative.eval x -
      standardGaussianPDF x * (x * p.eval x)) = 0 := by
    apply integral_eq_zero_of_hasDerivAt_of_integrable
      (f := fun x => standardGaussianPDF x * p.eval x)
    · intro x
      convert (hasDerivAt_standardGaussianPDF x).mul (p.hasDerivAt x) using 1
      ring
    · exact (integrable_standardGaussianPDF_mul_polynomial p.derivative).sub hxp
    · exact integrable_standardGaussianPDF_mul_polynomial p
  rw [integral_sub (integrable_standardGaussianPDF_mul_polynomial p.derivative) hxp] at hzero
  simpa only [standardGaussianMeasure,
    integral_gaussianReal_eq_integral_smul one_ne_zero,
    smul_eq_mul, standardGaussianPDF] using sub_eq_zero.mp hzero

/-- Moving a successor Hermite factor across the Gaussian inner product
differentiates the other polynomial. [OD14, §11.2, proof of Prop. 11.30]

**Proof sketch.** Apply Gaussian integration by parts to the product of the
preceding Hermite polynomial and the test polynomial. The Hermite recurrence
cancels the derivative of the Hermite factor. -/
private lemma integral_hermite_succ_mul_polynomial_standardGaussian (k : ℕ)
    (p : Polynomial ℝ) :
    (∫ x : ℝ, ((Polynomial.hermite (k + 1)).map (Int.castRingHom ℝ)).eval x * p.eval x
      ∂standardGaussianMeasure) =
      ∫ x : ℝ, ((Polynomial.hermite k).map (Int.castRingHom ℝ)).eval x *
        p.derivative.eval x ∂standardGaussianMeasure := by
  let H : Polynomial ℝ := (Polynomial.hermite k).map (Int.castRingHom ℝ)
  have h := integral_polynomial_derivative_standardGaussian (H * p)
  simp only [Polynomial.derivative_mul, Polynomial.eval_add] at h
  rw [integral_add
    (integrable_polynomial_eval_standardGaussian (H.derivative * p))
    (integrable_polynomial_eval_standardGaussian (H * p.derivative))] at h
  rw [Polynomial.hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
    ← Polynomial.derivative_map]
  change (∫ x, (Polynomial.X * H - H.derivative).eval x * p.eval x
      ∂standardGaussianMeasure) =
    ∫ x, H.eval x * p.derivative.eval x ∂standardGaussianMeasure
  simp only [← Polynomial.eval_mul, sub_mul, Polynomial.eval_sub]
  rw [integral_sub
    (integrable_polynomial_eval_standardGaussian ((Polynomial.X * H) * p))
    (integrable_polynomial_eval_standardGaussian (H.derivative * p))]
  simp only [Polynomial.eval_mul, Polynomial.eval_X, mul_assoc] at h ⊢
  linarith

/-- Pairing a polynomial with a degree-`k` Hermite polynomial equals the Gaussian
mean of its `k`th derivative. [OD14, §11.2, proof of Prop. 11.30]

**Proof sketch.** Repeatedly move a successor Hermite factor across the Gaussian
inner product, differentiating the test polynomial at each step. -/
lemma integral_hermite_mul_polynomial_standardGaussian (k : ℕ) (p : Polynomial ℝ) :
    (∫ x : ℝ, ((Polynomial.hermite k).map (Int.castRingHom ℝ)).eval x * p.eval x
      ∂standardGaussianMeasure) =
      ∫ x : ℝ, (Polynomial.derivative^[k] p).eval x ∂standardGaussianMeasure := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
      rw [integral_hermite_succ_mul_polynomial_standardGaussian, ih,
        Function.iterate_succ_apply]

/-- Differentiating a degree-`k` probabilists' Hermite polynomial `k` times
gives the constant `k!`. [OD14, Def. 11.29]

**Proof sketch.** The leading coefficient is one. The iterated derivative kills
the lower terms and multiplies the leading coefficient by the factorial. -/
private lemma iterate_derivative_hermite_self (k : ℕ) :
    Polynomial.derivative^[k] (Polynomial.hermite k) =
      Polynomial.C (k.factorial : ℤ) := by
  ext m
  rw [Polynomial.coeff_iterate_derivative]
  cases m with
  | zero =>
      simp [Nat.descFactorial_self, Polynomial.coeff_hermite_self]
  | succ m =>
      rw [Polynomial.coeff_hermite_of_lt (by omega : k < m.succ + k)]
      simp

/-- A degree-`k` Hermite polynomial is orthogonal to every polynomial of lower degree.
[OD14, Prop. 11.30]

**Proof sketch.** Move the Hermite factor to the `k`th derivative of the other
polynomial. That derivative vanishes because its degree is less than `k`. -/
lemma integral_hermite_mul_polynomial_eq_zero (k : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree < k) :
    (∫ x : ℝ, ((Polynomial.hermite k).map (Int.castRingHom ℝ)).eval x * p.eval x
      ∂standardGaussianMeasure) = 0 := by
  rw [integral_hermite_mul_polynomial_standardGaussian,
    Polynomial.iterate_derivative_eq_zero hp]
  simp

/-- Probabilists' Hermite polynomials are Gaussian orthogonal, with squared norm
`j!` in degree `j`. [OD14, Prop. 11.30]

**Proof sketch.** The higher-degree Hermite is orthogonal to the lower-degree
polynomial. In equal degrees the adjoint identity gives the constant factorial. -/
lemma integral_hermite_mul_hermite_standardGaussian (j k : ℕ) :
    (∫ x : ℝ, ((Polynomial.hermite j).map (Int.castRingHom ℝ)).eval x *
      ((Polynomial.hermite k).map (Int.castRingHom ℝ)).eval x
      ∂standardGaussianMeasure) = if j = k then (j.factorial : ℝ) else 0 := by
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · rw [if_neg (ne_of_lt hjk)]
    simpa only [mul_comm] using
      integral_hermite_mul_polynomial_eq_zero k
        ((Polynomial.hermite j).map (Int.castRingHom ℝ))
        ((Polynomial.natDegree_map_le).trans_lt
          (by simpa only [Polynomial.natDegree_hermite] using hjk))
  · rw [if_pos rfl, integral_hermite_mul_polynomial_standardGaussian]
    simp [Polynomial.iterate_derivative_map, iterate_derivative_hermite_self]
  · rw [if_neg (ne_of_gt hkj)]
    exact integral_hermite_mul_polynomial_eq_zero j
      ((Polynomial.hermite k).map (Int.castRingHom ℝ))
      ((Polynomial.natDegree_map_le).trans_lt
        (by simpa only [Polynomial.natDegree_hermite] using hkj))

/-- Normalized scalar Hermite polynomials are Gaussian orthonormal.
[OD14, Prop. 11.30]

**Proof sketch.** Divide the unnormalized orthogonality identity by the square
roots of the two factorials. Equal indices leave the factorial divided by itself. -/
lemma integral_normalizedHermite_mul_standardGaussian (j k : ℕ) :
    (∫ x : ℝ, (normalizedHermitePolynomial j).eval x *
      (normalizedHermitePolynomial k).eval x ∂standardGaussianMeasure) =
      if j = k then 1 else 0 := by
  simp only [normalizedHermitePolynomial, Polynomial.eval_mul, Polynomial.eval_C]
  conv_lhs =>
    arg 2
    ext x
    rw [mul_mul_mul_comm]
  rw [integral_const_mul, integral_hermite_mul_hermite_standardGaussian]
  by_cases h : j = k
  · subst k
    simp only [if_true]
    have hf : 0 < (j.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos j
    have hs : Real.sqrt (j.factorial : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hf)
    field_simp [hs]
    nlinarith [Real.sq_sqrt (le_of_lt hf)]
  · simp [h]

/-- The Gaussian inner product of multivariate Hermite functions is one for
equal multi-indices and zero otherwise. [OD14, Props. 11.30 and 11.33]

**Proof sketch.** Factor the product integral into scalar inner products. Each
factor is a Kronecker delta, so the product vanishes precisely when one index differs. -/
lemma integral_hermiteFunction_mul {n : ℕ} (α β : Fin n → ℕ) :
    (∫ x, hermiteFunction α x * hermiteFunction β x
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) =
      if α = β then 1 else 0 := by
  classical
  simp_rw [hermiteFunction_eq_prod, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun (i : Fin n) (x : ℝ) =>
    (normalizedHermitePolynomial (α i)).eval x *
      (normalizedHermitePolynomial (β i)).eval x)]
  simp_rw [integral_normalizedHermite_mul_standardGaussian]
  by_cases h : α = β
  · simp [h]
  · rw [if_neg h]
    simp only [funext_iff, not_forall] at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Multiplication by a standard Gaussian coordinate transfers to the derivative
of a polynomial evaluated along an affine map.
[OD14, §11.2, Gaussian integration by parts]

**Proof sketch.** Apply polynomial Gaussian integration by parts to the affine
composition. The polynomial chain rule supplies the affine map's slope. -/
lemma integral_id_mul_polynomial_affine_standardGaussian
    (p : Polynomial ℝ) (a b : ℝ) :
    (∫ y : ℝ, y * p.eval (a + b * y) ∂standardGaussianMeasure) =
      b * ∫ y : ℝ, p.derivative.eval (a + b * y) ∂standardGaussianMeasure := by
  have h := (integral_polynomial_derivative_standardGaussian
    (p.comp (Polynomial.C a + Polynomial.C b * Polynomial.X))).symm
  simp_rw [Polynomial.derivative_comp, Polynomial.derivative_add,
    Polynomial.derivative_C, Polynomial.derivative_C_mul_X, zero_add,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] at h
  simp_rw [integral_const_mul, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at h
  exact h

/-- A polynomial times a polynomial evaluated along an affine map is integrable
against the standard Gaussian measure.

**Proof sketch.** The product is the evaluation of a single composed polynomial,
so the existing Gaussian polynomial integrability theorem applies. -/
lemma integrable_polynomial_mul_affine_standardGaussian
    (p q : Polynomial ℝ) (a b : ℝ) :
    Integrable (fun y : ℝ => q.eval y * p.eval (a + b * y))
      standardGaussianMeasure := by
  convert integrable_polynomial_eval_standardGaussian
    (q * p.comp (Polynomial.C a + Polynomial.C b * Polynomial.X)) using 1
  simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X]

end BooleanAnalysis.GaussianSpace
