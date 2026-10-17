/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.ProductDensity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Moment bounds for product Gaussian derivative kernels

## Main definitions

The first and second coordinate scores are written using the existing Gaussian
means and variance; no new Gaussian measure or differential operator is defined.

## Main results

* Centered coordinate first scores times bounded measurable functions are
  integrable, with a uniform absolute-integral bound.
* The corresponding Hessian scores have genuine integrability and a uniform
  absolute-integral bound twice the inverse variance.

Both estimates follow from existing coordinate second moments and explicit
quadratic majorants. These constants suffice for bounded Lipschitz derivatives
of Gaussian averages.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian moments, and §11.4,
  the smooth indicator approximation for Gaussian isoperimetry.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace BooleanAnalysis.GaussianSpace

/-- A bounded measurable function times a centered Gaussian coordinate divided
by the variance is integrable, with absolute integral at most one plus the
inverse variance. [OD14, §11.1; §11.4, Gaussian smoothing]

**Proof sketch.** Bound the centered absolute coordinate by its square plus
one. The resulting quadratic is integrable and its expectation is the
variance plus one. Domination proves genuine integrability and the integral
bound. The constant is a convenient nonsharp estimate. -/
lemma gaussianCoordinate_first_kernel_integrable_bound {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1) (i : ι) :
    Integrable (fun z : ι → ℝ => (z i - c i) / v * f z)
      (Measure.pi fun j => gaussianReal (c j) v) ∧
      |∫ z : ι → ℝ, (z i - c i) / v * f z
        ∂(Measure.pi fun j => gaussianReal (c j) v)| ≤ 1 + 1 / (v : ℝ) := by
  have hv' : 0 < (v : ℝ) := by positivity
  have hi := integrable_centered_sq_gaussianCoordinate c v i
  let B (z : ι → ℝ) := ((z i - c i) ^ 2 + 1) / (v : ℝ)
  have hB : Integrable B (Measure.pi fun j => gaussianReal (c j) v) :=
    (hi.add (integrable_const 1)).div_const _
  have hbound (z : ι → ℝ) : ‖(z i - c i) / v * f z‖ ≤ B z := by
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hv']
    refine (mul_le_of_le_one_right (by positivity) (hfbound z)).trans ?_
    apply div_le_div_of_nonneg_right _ hv'.le
    change |z i - c i| ≤ (z i - c i) ^ 2 + 1
    nlinarith [sq_nonneg (|z i - c i| - 1 / 2), sq_abs (z i - c i)]
  have hint : Integrable (fun z : ι → ℝ => (z i - c i) / v * f z)
      (Measure.pi fun j => gaussianReal (c j) v) :=
    hB.mono' (by fun_prop) (Eventually.of_forall hbound)
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ z : ι → ℝ, |(z i - c i) / v * f z|
        ∂(Measure.pi fun j => gaussianReal (c j) v) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := Measure.pi fun j => gaussianReal (c j) v)
        (fun z : ι → ℝ => (z i - c i) / v * f z)
    _ ≤ ∫ z : ι → ℝ, B z ∂(Measure.pi fun j => gaussianReal (c j) v) :=
      integral_mono hint.abs hB (fun z => by simpa only [Real.norm_eq_abs] using hbound z)
    _ = 1 + 1 / (v : ℝ) := by
      dsimp [B]
      rw [integral_div, integral_add hi (integrable_const 1),
        integral_centered_sq_gaussianCoordinate, integral_const]
      simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
      field_simp

/-- A coordinate Hessian score times a scalar bounded by one is dominated by
a nonnegative quadratic in those coordinates.
[OD14, §11.1; §11.4, Gaussian smoothing]

**Proof sketch.** Bound the product of the centered coordinates by half the
sum of their squares, and bound the diagonal correction by the inverse variance. -/
lemma abs_productHessian_mul_le {ι : Type*} [DecidableEq ι]
    (c z : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) (i j : ι) (a : ℝ) (ha : |a| ≤ 1) :
    |(((z i - c i) * (z j - c j) / (v : ℝ) ^ 2 -
      if i = j then 1 / (v : ℝ) else 0) * a)| ≤
      ((z i - c i) ^ 2 + (z j - c j) ^ 2) / (2 * (v : ℝ) ^ 2) + 1 / v := by
  have hv' : 0 < (v : ℝ) := by positivity
  have hab : |(z i - c i) * (z j - c j)| ≤
      ((z i - c i) ^ 2 + (z j - c j) ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|z i - c i| - |z j - c j|),
      sq_abs (z i - c i), sq_abs (z j - c j)]
  have hdelta : |if i = j then 1 / (v : ℝ) else 0| ≤ 1 / (v : ℝ) := by
    split_ifs <;> simp [hv'.le]
  rw [abs_mul]
  calc
    _ ≤ |(z i - c i) * (z j - c j) / (v : ℝ) ^ 2 -
        if i = j then 1 / (v : ℝ) else 0| :=
      mul_le_of_le_one_right (abs_nonneg _) ha
    _ ≤ |(z i - c i) * (z j - c j) / (v : ℝ) ^ 2| +
        |if i = j then 1 / (v : ℝ) else 0| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_div, abs_of_nonneg (sq_nonneg (v : ℝ))]
      convert add_le_add (div_le_div_of_nonneg_right hab (sq_nonneg (v : ℝ))) hdelta using 1
      ring

/-- The quadratic dominating a coordinate Gaussian Hessian score is integrable
under the Gaussian product law. [OD14, §11.1, Gaussian product moments]

**Proof sketch.** Both centered coordinate squares have finite integrals;
combine them linearly with the constant inverse-variance term. -/
lemma integrable_productHessian_bound {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ℝ≥0) (i j : ι) :
    Integrable (fun z : ι → ℝ =>
      ((z i - c i) ^ 2 + (z j - c j) ^ 2) / (2 * (v : ℝ) ^ 2) + 1 / v)
      (Measure.pi fun k => gaussianReal (c k) v) :=
  (((integrable_centered_sq_gaussianCoordinate c v i).add
    (integrable_centered_sq_gaussianCoordinate c v j)).div_const _).add (integrable_const _)

/-- The Gaussian expectation of the quadratic Hessian-score bound is twice the
inverse variance. [OD14, §11.1, Gaussian product moments]

**Proof sketch.** Substitute the variance for each centered coordinate second
moment and use probability normalization for the constant term. -/
lemma integral_productHessian_bound {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) (i j : ι) :
    (∫ z : ι → ℝ,
      ((z i - c i) ^ 2 + (z j - c j) ^ 2) / (2 * (v : ℝ) ^ 2) + 1 / v
      ∂(Measure.pi fun k => gaussianReal (c k) v)) = 2 / (v : ℝ) := by
  have hi := integrable_centered_sq_gaussianCoordinate c v i
  have hj := integrable_centered_sq_gaussianCoordinate c v j
  have hq : Integrable (fun z : ι → ℝ =>
      ((z i - c i) ^ 2 + (z j - c j) ^ 2) / (2 * (v : ℝ) ^ 2))
      (Measure.pi fun k => gaussianReal (c k) v) := (hi.add hj).div_const _
  rw [integral_add hq (integrable_const _), integral_div,
    integral_add hi hj, integral_centered_sq_gaussianCoordinate,
    integral_centered_sq_gaussianCoordinate, integral_const]
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  field_simp
  ring

/-- Every coordinate Gaussian Hessian score times a bounded measurable
function is genuinely integrable. [OD14, §11.4, Gaussian smoothing]

**Proof sketch.** The integrand is measurable and its absolute value is
bounded by the integrable quadratic computed above. -/
lemma integrable_productHessian_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1) (i j : ι) :
    Integrable (fun z : ι → ℝ => (((z i - c i) * (z j - c j) / (v : ℝ) ^ 2 -
      if i = j then 1 / (v : ℝ) else 0) * f z))
      (Measure.pi fun k => gaussianReal (c k) v) := by
  refine (integrable_productHessian_bound c v i j).mono' ?_
    (Eventually.of_forall fun z => ?_)
  · exact (Measurable.mul (by fun_prop) hf).aestronglyMeasurable
  · simpa only [Real.norm_eq_abs] using abs_productHessian_mul_le c z v hv i j (f z) (hfbound z)

/-- The absolute integral of any coordinate Gaussian Hessian score times a
function bounded by one is at most twice the inverse variance.
[OD14, §11.4, Gaussian smoothing]

**Proof sketch.** The absolute integral is bounded by the integral absolute
value, then by the quadratic majorant whose expectation is twice the inverse
variance. This bound also holds for the totalized integral; the preceding
result supplies genuine integrability for measurable inputs. -/
lemma abs_integral_productHessian_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) {f : (ι → ℝ) → ℝ}
    (hfbound : ∀ z, |f z| ≤ 1) (i j : ι) :
    |∫ z : ι → ℝ, (((z i - c i) * (z j - c j) / (v : ℝ) ^ 2 -
      if i = j then 1 / (v : ℝ) else 0) * f z)
      ∂(Measure.pi fun k => gaussianReal (c k) v)| ≤ 2 / (v : ℝ) := by
  calc
    _ ≤ ∫ z : ι → ℝ, |(((z i - c i) * (z j - c j) / (v : ℝ) ^ 2 -
        if i = j then 1 / (v : ℝ) else 0) * f z)|
        ∂(Measure.pi fun k => gaussianReal (c k) v) := abs_integral_le_integral_abs
    _ ≤ ∫ z : ι → ℝ,
        ((z i - c i) ^ 2 + (z j - c j) ^ 2) / (2 * (v : ℝ) ^ 2) + 1 / v
        ∂(Measure.pi fun k => gaussianReal (c k) v) :=
      integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
        (integrable_productHessian_bound c v i j)
        (Eventually.of_forall fun z => abs_productHessian_mul_le c z v hv i j (f z) (hfbound z))
    _ = _ := integral_productHessian_bound c v hv i j

end BooleanAnalysis.GaussianSpace
