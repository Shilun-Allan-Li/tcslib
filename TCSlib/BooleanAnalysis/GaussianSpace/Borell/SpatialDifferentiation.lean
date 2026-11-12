/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.NoiseDefinitions
import Mathlib.Analysis.Calculus.ParametricIntegral
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Spatial derivatives of Gaussian averaging

## Main definitions

The existing Gaussian probability law, noise operator, and profile are reused.

## Main results

* `hasFDerivAt_integral_affine_gaussianPi`.
* `hasFDerivAt_gaussianNoise_of_contDiff_bounded`.
* `hasFDerivAt_fderiv_gaussianNoise_of_contDiff_bounded`.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2.
-/

open MeasureTheory Filter
open scoped Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1))
/-- For a bounded C1 function with bounded derivative, affine Gaussian
averaging is differentiable, with derivative the average of the affine-scaled
derivative. The codomain may be any complete real normed space.

**Proof sketch.** The chain rule gives the integrand derivative. Its norm is
uniformly bounded by the scale times the derivative bound. This constant is
integrable under the Gaussian probability law, so differentiation under the
integral applies. -/
lemma hasFDerivAt_integral_affine_gaussianPi {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : (Fin n → ℝ) → E} (hf : ContDiff ℝ 1 f) {B M : ℝ}
    (hb : ∀ z, ‖f z‖ ≤ B) (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (r s : ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fun x => ∫ y : Fin n → ℝ, f (r • x + s • y)
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure))
      (∫ y : Fin n → ℝ, r • fderiv ℝ f (r • x + s • y)
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) x := by
  let μ := Measure.pi fun _ : Fin n => standardGaussianMeasure
  haveI : IsProbabilityMeasure standardGaussianMeasure :=
    inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1))
  have hd (z y : Fin n → ℝ) :
      HasFDerivAt (fun x => f (r • x + s • y))
        (r • fderiv ℝ f (r • z + s • y)) z := by
    convert (hf.differentiable le_rfl (r • z + s • y)).hasFDerivAt.comp z
      (((hasFDerivAt_id z).const_smul r).add_const (s • y)) using 1
    ext v
    simp
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (ε := 1) (F' := fun z y => r • fderiv ℝ f (r • z + s • y))
    (bound := fun _ => |r| * M) zero_lt_one
  · exact Eventually.of_forall fun z => (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact Integrable.of_bound (hf.continuous.comp (by fun_prop)).aestronglyMeasurable B
      (Eventually.of_forall fun y => hb _)
  · exact (((hf.continuous_fderiv le_rfl).comp (by fun_prop)).const_smul r).aestronglyMeasurable
  · exact Eventually.of_forall fun y z _ => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hm _) (abs_nonneg r)
  · exact integrable_const _
  · exact Eventually.of_forall fun y z _ => hd z y


/-- The spatial derivative of Gaussian noise on a bounded C1 function is
the correlation times the average of its derivative.
[MN15, §2, commutation of gradient and Ornstein–Uhlenbeck averaging] -/
lemma hasFDerivAt_gaussianNoise_of_contDiff_bounded {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {B M : ℝ}
    (hb : ∀ z, |f z| ≤ B) (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (r : ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (gaussianNoise r f)
      (r • ∫ y : Fin n → ℝ, fderiv ℝ f
        (r • x + Real.sqrt (1-r^2) • y)
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) x := by
  have h := hasFDerivAt_integral_affine_gaussianPi hf
    (fun z => by simpa only [Real.norm_eq_abs] using hb z) hm r (Real.sqrt (1-r^2)) x
  rw [integral_smul] at h
  exact h

/-- The second spatial derivative of Gaussian noise on a bounded C2 function
with bounded first and second derivatives is the squared correlation times
the average of its second derivative.
[MN15, §2, commutation of derivatives and Ornstein–Uhlenbeck averaging] -/
lemma hasFDerivAt_fderiv_gaussianNoise_of_contDiff_bounded {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {B M K : ℝ}
    (hb : ∀ z, |f z| ≤ B) (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (hk : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K)
    (r : ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fderiv ℝ (gaussianNoise r f))
      (r^2 • ∫ y : Fin n → ℝ, fderiv ℝ (fderiv ℝ f)
        (r • x + Real.sqrt (1-r^2) • y)
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) x := by
  have heq : fderiv ℝ (gaussianNoise r f) = fun z =>
      r • ∫ y : Fin n → ℝ, fderiv ℝ f
        (r • z + Real.sqrt (1-r^2) • y)
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
    funext z
    exact (hasFDerivAt_gaussianNoise_of_contDiff_bounded
      (hf.of_le (by norm_num)) hb hm r z).fderiv
  rw [heq]
  have h := (hasFDerivAt_integral_affine_gaussianPi
    (hf.fderiv_right (by norm_num)) hm hk r (Real.sqrt (1-r^2)) x).const_smul r
  simpa only [integral_smul, smul_smul, pow_two] using h


/-- The derivative of Gaussian noise is bounded by the absolute correlation
times the initial derivative bound. [MN15, §2, derivative commutation] -/
lemma norm_fderiv_gaussianNoise_commutation_le {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {B M : ℝ}
    (hb : ∀ z, |f z| ≤ B) (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (r : ℝ) (x : Fin n → ℝ) :
    ‖fderiv ℝ (gaussianNoise r f) x‖ ≤ |r| * M := by
  rw [(hasFDerivAt_gaussianNoise_of_contDiff_bounded hf hb hm r x).fderiv,
    norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg r)
  simpa only [measureReal_univ_eq_one, mul_one] using
    (norm_integral_le_of_norm_le_const
      (μ := Measure.pi fun _ : Fin n => standardGaussianMeasure)
      (Eventually.of_forall fun y => hm (r • x + Real.sqrt (1-r^2) • y)))

/-- The second derivative of Gaussian noise is bounded by the squared
correlation times the initial bound. [MN15, §2, derivative commutation] -/
lemma norm_fderiv_fderiv_gaussianNoise_commutation_le {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {B M K : ℝ}
    (hb : ∀ z, |f z| ≤ B) (hm : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (hk : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K)
    (r : ℝ) (x : Fin n → ℝ) :
    ‖fderiv ℝ (fderiv ℝ (gaussianNoise r f)) x‖ ≤ r^2 * K := by
  letI : NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) := inferInstance
  rw [(hasFDerivAt_fderiv_gaussianNoise_of_contDiff_bounded hf hb hm hk r x).fderiv,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
  simpa only [measureReal_univ_eq_one, mul_one] using
    (norm_integral_le_of_norm_le_const
      (μ := Measure.pi fun _ : Fin n => standardGaussianMeasure)
      (Eventually.of_forall fun y => hk (r • x + Real.sqrt (1-r^2) • y)))


end BooleanAnalysis.GaussianSpace
