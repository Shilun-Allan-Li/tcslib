/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.IndicatorSmoothing
import TCSlib.BooleanAnalysis.GaussianSpace.ProductHessian

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Regularity of averaged Gaussian indicators

## Main definitions

The existing averaged indicator and ordinary Fréchet derivative are reused.

## Main results

* Averaged indicators at nonzero sine angles have a product-density integral
  representation against a fixed Lebesgue measure.
* Differentiating that density gives the ordinary Fréchet derivative, with an
  explicit global norm bound and Lipschitz constant for each such angle.

This representation moves the measurable indicator out of the parameterized
argument before differentiating the smooth Gaussian density.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian smoothing, and §11.4,
  the smooth indicator approximation for Gaussian isoperimetry.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- At a nonzero sine angle, an averaged Gaussian indicator equals its integral
against the affine Gaussian product density, with mean cos(u) times the input
and variance sin(u) squared. [OD14, §11.1; §11.4, Gaussian indicator smoothing]

**Proof sketch.** Apply the affine product Gaussian integration formula to the
measurable indicator. Its mean and variance are the rotation coupling's
coordinate mean and squared noise scale. -/
lemma averagedGaussianIndicator_eq_integral_density {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (u : ℝ)
    (hu : Real.sin u ≠ 0) (x : Fin n → ℝ) :
    averagedGaussianIndicator A u x =
      ∫ z : Fin n → ℝ,
        (∏ i, gaussianPDFReal (Real.cos u * x i)
          ⟨Real.sin u ^ 2, sq_nonneg _⟩ (z i)) * A.indicator (fun _ => (1 : ℝ)) z
        ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
  unfold averagedGaussianIndicator
  exact integral_affine_gaussian_pi_eq_density (fun i => Real.cos u * x i)
    (Real.sin u) hu (measurable_const.indicator hA)

/-- Cosine scaling of a finite real product has operator norm at most one. -/
private lemma norm_cosineScaling_le_one (n : ℕ) (u : ℝ) :
    ‖(Real.cos u • ContinuousLinearMap.id ℝ (Fin n → ℝ))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    norm_smul, Real.norm_eq_abs, one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one u)

/-- An averaged measurable Gaussian indicator is differentiable at every
input when the noise scale is nonzero, with derivative given by the product
density derivative composed with the cosine scaling map.
[OD14, §11.1; §11.4, Gaussian indicator smoothing]

**Proof sketch.** Write the average against its translated product density.
The bounded measurable indicator permits differentiation under the integral
in the mean vector. Compose that derivative with multiplication of the input
by the cosine of the angle. -/
lemma hasFDerivAt_averagedGaussianIndicator {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (u : ℝ)
    (hu : Real.sin u ≠ 0) (x : Fin n → ℝ) :
    HasFDerivAt (averagedGaussianIndicator A u)
      ((∫ z : Fin n → ℝ, A.indicator (fun _ => (1 : ℝ)) z •
        gaussianProductDensityDerivative ⟨Real.sin u ^ 2, sq_nonneg _⟩
          (fun i => Real.cos u * x i) z
        ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ))).comp
          (Real.cos u • ContinuousLinearMap.id ℝ (Fin n → ℝ))) x := by
  classical
  let v : ℝ≥0 := ⟨Real.sin u ^ 2, sq_nonneg _⟩
  have hv : v ≠ 0 := by
    intro h
    have hsq : Real.sin u ^ 2 = 0 := congrArg Subtype.val h
    exact hu (eq_zero_of_pow_eq_zero hsq)
  have hfbound (z : Fin n → ℝ) : |A.indicator (fun _ => (1 : ℝ)) z| ≤ 1 := by
    by_cases hz : z ∈ A <;> simp [hz]
  have hf := hasFDerivAt_integral_gaussianProductDensity
    (measurable_const.indicator hA) hfbound v hv (fun i => Real.cos u * x i)
  have hc : HasFDerivAt (fun y : Fin n → ℝ => fun i => Real.cos u * y i)
      (Real.cos u • ContinuousLinearMap.id ℝ (Fin n → ℝ)) x := by
    simpa only [Pi.smul_apply, smul_eq_mul] using (hasFDerivAt_id x).const_smul (Real.cos u)
  apply (hf.comp x hc).congr_of_eventuallyEq
  exact Eventually.of_forall fun y =>
    averagedGaussianIndicator_eq_integral_density hA u hu y

/-- At every nonzero sine angle, the derivative of an averaged measurable
Gaussian indicator is uniformly bounded in the input by the dimension times
one plus the inverse noise variance. [OD14, §11.1; §11.4, Gaussian smoothing]
The explicit constant is a convenient nonsharp bound.

**Proof sketch.** Use the density derivative formula. The derivative integral
has the uniform product Gaussian bound, and composing with cosine scaling
cannot increase its operator norm. -/
lemma norm_fderiv_averagedGaussianIndicator_le {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (u : ℝ)
    (hu : Real.sin u ≠ 0) (x : Fin n → ℝ) :
    ‖fderiv ℝ (averagedGaussianIndicator A u) x‖ ≤
      (n : ℝ) * (1 + 1 / (Real.sin u ^ 2)) := by
  classical
  let v : ℝ≥0 := ⟨Real.sin u ^ 2, sq_nonneg _⟩
  have hv : v ≠ 0 := by
    intro h
    have hsq : Real.sin u ^ 2 = 0 := congrArg Subtype.val h
    exact hu (eq_zero_of_pow_eq_zero hsq)
  have hfbound (z : Fin n → ℝ) : |A.indicator (fun _ => (1 : ℝ)) z| ≤ 1 := by
    by_cases hz : z ∈ A <;> simp [hz]
  rw [(hasFDerivAt_averagedGaussianIndicator hA u hu x).fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_of_le_one_right (norm_nonneg _) (norm_cosineScaling_le_one n u)).trans ?_
  simpa only [Fintype.card_fin] using
    norm_integral_gaussianProductDensityDerivative_smul_le
      (measurable_const.indicator hA) hfbound v hv (fun i => Real.cos u * x i)

/-- Pulling a linear-map family back through a linear contraction, and
precomposing its values with that contraction, preserves its Lipschitz bound.

**Proof sketch.** The norm of the difference of the composed maps is bounded
by the old difference times the contraction's norm. Apply the original
Lipschitz bound and the contraction bound once more in the input. -/
private lemma lipschitzWith_comp_contraction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {D : E → E →L[ℝ] ℝ} {C : ℝ≥0}
    (hD : LipschitzWith C D) (L : E →L[ℝ] E) (hL : ‖L‖ ≤ 1) :
    LipschitzWith C (fun x => (D (L x)).comp L) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.sub_comp]
  have hpoint : ‖L x - L y‖ ≤ ‖x - y‖ := by
    rw [← map_sub]
    exact (L.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hL)
  calc
    _ ≤ ‖D (L x) - D (L y)‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖D (L x) - D (L y)‖ := mul_le_of_le_one_right (norm_nonneg _) hL
    _ ≤ (C : ℝ) * ‖L x - L y‖ := hD.norm_sub_le _ _
    _ ≤ (C : ℝ) * ‖x - y‖ := mul_le_mul_of_nonneg_left hpoint C.coe_nonneg

/-- At a nonzero sine angle, the derivative of an averaged measurable Gaussian
indicator is globally Lipschitz, with constant twice the squared dimension
divided by the noise variance. [OD14, §11.1; §11.4, Gaussian indicator smoothing]
The dimension factor is a convenient nonsharp bound.

**Proof sketch.** The derivative of the product Gaussian average is globally
Lipschitz by its uniform Hessian bound. Its pullback and precomposition by
cosine scaling preserve this bound, since cosine scaling is a contraction.
The derivative formula identifies this pullback with the ordinary derivative
of the averaged indicator. -/
lemma lipschitzWith_fderiv_averagedGaussianIndicator {n : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (u : ℝ)
    (hu : Real.sin u ≠ 0) :
    LipschitzWith ((n : ℝ≥0) ^ 2 * (2 / ⟨Real.sin u ^ 2, sq_nonneg _⟩))
      (fderiv ℝ (averagedGaussianIndicator A u)) := by
  classical
  let v : ℝ≥0 := ⟨Real.sin u ^ 2, sq_nonneg _⟩
  have hv : v ≠ 0 := by
    intro h
    have hsq : Real.sin u ^ 2 = 0 := congrArg Subtype.val h
    exact hu (eq_zero_of_pow_eq_zero hsq)
  have hfbound (z : Fin n → ℝ) : |A.indicator (fun _ => (1 : ℝ)) z| ≤ 1 := by
    by_cases hz : z ∈ A <;> simp [hz]
  let D (c : Fin n → ℝ) := ∫ z : Fin n → ℝ,
    A.indicator (fun _ => (1 : ℝ)) z • gaussianProductDensityDerivative v c z
      ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ))
  have hD : LipschitzWith ((n : ℝ≥0) ^ 2 * (2 / v)) D := by
    simpa only [Fintype.card_fin] using
      lipschitzWith_integral_gaussianProductDensityDerivative
        (measurable_const.indicator hA) hfbound v hv
  have h := lipschitzWith_comp_contraction hD
    (Real.cos u • ContinuousLinearMap.id ℝ (Fin n → ℝ)) (norm_cosineScaling_le_one n u)
  convert h using 1
  funext x
  exact (hasFDerivAt_averagedGaussianIndicator hA u hu x).fderiv

end BooleanAnalysis.GaussianSpace
