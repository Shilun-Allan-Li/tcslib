/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.NoiseDefinitions
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariables.Moments
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.MvPolynomial.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian averages of polynomial inputs

## Main definitions

The existing multilinear-polynomial evaluation and Gaussian law are reused.

## Main results

* `integrable_gaussian_affine_monomial`: integrability of translated monomials.
* `integral_gaussian_affine_monomial`: their expectations are products of means.
* `memLp_eval_gaussian`: all finite moments of ordinary polynomial evaluations.
* `exists_real_polynomial_re`: real parts of complex polynomials at real inputs.
* `exists_polynomial_eval_linear`: polynomial representation of real-linear forms.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Fact 11.13 and Theorem 11.22.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions Hypercontractivity

variable {n : ℕ}
local notation "γ" => (Measure.pi fun _ : Fin n => standardGaussianMeasure)

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- A multilinear monomial in affine Gaussian coordinates is integrable.
[OD14, Fact 11.13]

**Proof sketch.** Extend the product by the constant one on missing coordinates.
Each scalar affine factor is integrable, so the finite product theorem applies. -/
lemma integrable_gaussian_affine_monomial (a : Fin n → ℝ) (s : ℝ) (S : Finset (Fin n)) :
    Integrable (fun y : Fin n → ℝ => ∏ i ∈ S, (a i + s * y i)) γ := by
  classical
  have hi (i : Fin n) : Integrable (fun y : ℝ => if i ∈ S then a i + s * y else 1)
      standardGaussianMeasure := by
    by_cases h : i ∈ S
    · simpa only [if_pos h] using (integrable_const (a i)).add
        (((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).const_mul s)
    · simpa only [if_neg h] using (integrable_const (1 : ℝ))
  convert Integrable.fintype_prod hi using 1
  funext y
  simp only [Fintype.prod_ite_mem]

/-- The expectation of an affine Gaussian monomial is the product of its means.
[OD14, Fact 11.13]

**Proof sketch.** Extend missing factors by one and factor the product integral
over the independent coordinates. The centered Gaussian terms integrate to zero. -/
lemma integral_gaussian_affine_monomial (a : Fin n → ℝ) (s : ℝ) (S : Finset (Fin n)) :
    (∫ y : Fin n → ℝ, ∏ i ∈ S, (a i + s * y i) ∂γ) = ∏ i ∈ S, a i := by
  classical
  let g := fun (i : Fin n) (y : ℝ) => if i ∈ S then a i + s * y else 1
  have hi (i : Fin n) : (∫ y, g i y ∂standardGaussianMeasure) =
      if i ∈ S then a i else 1 := by
    by_cases h : i ∈ S
    · simp only [g, if_pos h, standardGaussianMeasure]
      change (∫ y : ℝ, a i + s * id y ∂gaussianReal 0 1) = a i
      rw [integral_add (integrable_const (a i))
        (((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).const_mul s),
        integral_const_mul]
      simp [integral_id_gaussianReal]
    · simp [g, h]
  calc
    _ = ∫ y, ∏ i, g i (y i) ∂γ := by simp only [g, Fintype.prod_ite_mem]
    _ = ∏ i, ∫ y, g i y ∂standardGaussianMeasure := integral_fintype_prod_eq_prod g
    _ = _ := by simp only [hi, Fintype.prod_ite_mem]

/-- Every real or complex multivariate polynomial has all finite Gaussian moments
when evaluated at real Gaussian inputs.
[OD14, §11.1, preceding Thm. 11.22]

**Proof sketch.** Gaussian coordinates have every finite moment. Induct on
constants, sums and multiplication by variables, using Hölder at twice the
requested exponent for each multiplication. -/
lemma memLp_eval_gaussian {𝕜 : Type*} [RCLike 𝕜] (P : MvPolynomial (Fin n) 𝕜)
    {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun x : Fin n → ℝ => MvPolynomial.eval (fun i => (x i : 𝕜)) P) p γ := by
  induction P using MvPolynomial.induction_on generalizing p with
  | C c => simpa only [MvPolynomial.eval_C] using memLp_const c
  | add P Q hP hQ => simpa only [MvPolynomial.eval_add] using (hP hp).add (hQ hp)
  | mul_X P i hP =>
    letI : ENNReal.HolderTriple (2 * p) (2 * p) p := ⟨by
      rw [ENNReal.mul_inv (by simp) (by simp), ← two_mul, ← mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
    have hptop : 2 * p ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hp
    have hi : MemLp (fun x : Fin n → ℝ => (x i : 𝕜)) (2 * p) γ :=
      ((memLp_id_gaussianReal' (μ := 0) (v := 1) (2 * p) hptop).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin n => standardGaussianMeasure) i)).ofReal
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hi.mul' (hP hptop)

/-- Taking the real part of a complex polynomial at real inputs is represented by
a real polynomial.

**Proof sketch.** Taking real coefficient parts commutes with sums and with
multiplication by the real coordinate variables. -/
lemma exists_real_polynomial_re (P : MvPolynomial (Fin n) ℂ) :
    ∃ Q : MvPolynomial (Fin n) ℝ, ∀ x : Fin n → ℝ,
      MvPolynomial.eval x Q = (MvPolynomial.eval (fun i => (x i : ℂ)) P).re := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨MvPolynomial.C c.re, fun _ => by simp⟩
  | add P Q hP hQ =>
    obtain ⟨P', hP'⟩ := hP
    obtain ⟨Q', hQ'⟩ := hQ
    exact ⟨P' + Q', fun x => by
      simp only [MvPolynomial.eval_add, hP', hQ', Complex.add_re]⟩
  | mul_X P i hP =>
    obtain ⟨P', hP'⟩ := hP
    exact ⟨P' * MvPolynomial.X i, fun x => by
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, hP', Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]⟩

/-- Every complex-valued real-linear form on finite real coordinate space is the
evaluation of a complex multivariate polynomial. -/
lemma exists_polynomial_eval_linear (L : (Fin n → ℝ) →L[ℝ] ℂ) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ x : Fin n → ℝ,
      MvPolynomial.eval (fun i => (x i : ℂ)) P = L x := by
  classical
  refine ⟨∑ i, MvPolynomial.C (L (Pi.single i 1)) * MvPolynomial.X i, ?_⟩
  intro x
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin n → ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, map_sum, map_smul, Complex.real_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

end BooleanAnalysis.GaussianSpace
