/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.NoiseDefinitions
import TCSlib.BooleanAnalysis.GaussianSpace.ProductHessian
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform spatial bounds for Gaussian smoothing

## Main definitions

The existing Gaussian noise and product-density derivatives are reused.

## Main results

Uniform first and second derivative bounds for Gaussian noise applied to
measurable functions bounded in absolute value by one.

## References

* [MN15] E. Mossel and J. Neeman, *Robust optimality of Gaussian noise stability*,
  Journal of the European Mathematical Society 17 (2015), 433–482, §2.
-/
open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace BooleanAnalysis.GaussianSpace
open ThresholdFunctions
/-- Scaling by a valid correlation has operator norm at most one. -/
lemma norm_gaussianScaling_le_one {n : ℕ} {r : ℝ} (hr : r ∈ Set.Icc (-1 : ℝ) 1) :
    ‖r • ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    norm_smul, Real.norm_eq_abs, one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr hr)
/-- The derivative of Gaussian noise of a bounded measurable function is
the averaged Gaussian density derivative composed with correlation scaling.
[MN15, §2, regularization]

**Proof sketch.** Write Gaussian noise using its affine Gaussian density.
Differentiate its mean parameter using the product-density theorem, then
compose with correlation scaling. -/
lemma hasFDerivAt_gaussianNoise_density {n : ℕ} {r : ℝ}
    (hr : r ∈ Set.Ioo (-1 : ℝ) 1) {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hbound : ∀ z, |f z| ≤ 1) (x : Fin n → ℝ) :
    HasFDerivAt (gaussianNoise r f)
      ((∫ z : Fin n → ℝ, f z • gaussianProductDensityDerivative
          ⟨1 - r ^ 2, by nlinarith [hr.1, hr.2]⟩
          (fun i => r * x i) z ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ))).comp
        (r • ContinuousLinearMap.id ℝ (Fin n → ℝ))) x := by
  classical
  let v : ℝ≥0 := ⟨1 - r ^ 2, by nlinarith [hr.1, hr.2]⟩
  have hv : v ≠ 0 := by
    have : 0 < (v : ℝ) := by dsimp [v]; nlinarith [hr.1, hr.2]
    exact ne_of_gt (show 0 < v from this)
  have hs : Real.sqrt (1 - r ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (by nlinarith [hr.1, hr.2])).ne'
  have hd := hasFDerivAt_integral_gaussianProductDensity hf hbound v hv
    (fun i => r * x i)
  have hc : HasFDerivAt (fun y : Fin n → ℝ => fun i => r * y i)
      (r • ContinuousLinearMap.id ℝ (Fin n → ℝ)) x := by
    simpa only [Pi.smul_apply, smul_eq_mul] using (hasFDerivAt_id x).const_smul r
  apply (hd.comp x hc).congr_of_eventuallyEq
  apply Eventually.of_forall
  intro y
  rw [gaussianNoise_eq]
  have hvariance : (⟨Real.sqrt (1 - r ^ 2) ^ 2, sq_nonneg _⟩ : ℝ≥0) = v := by
    apply Subtype.ext
    exact Real.sq_sqrt (by nlinarith [hr.1, hr.2])
  simpa only [hvariance] using integral_affine_gaussian_pi_eq_density
    (fun i => r * y i) (Real.sqrt (1 - r ^ 2)) hs hf
/-- The first derivative of Gaussian smoothing of a function bounded by one
is uniformly bounded by `n * (1 + 1/(1-r²))`.
[MN15, §2, bounded derivatives after regularization; nonoptimal explicit bound] -/
lemma norm_fderiv_gaussianNoise_le {n : ℕ} {r : ℝ}
    (hr : r ∈ Set.Ioo (-1 : ℝ) 1) {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hbound : ∀ z, |f z| ≤ 1) (x : Fin n → ℝ) :
    ‖fderiv ℝ (gaussianNoise r f) x‖ ≤ (n : ℝ) * (1 + 1 / (1 - r ^ 2)) := by
  rw [(hasFDerivAt_gaussianNoise_density hr hf hbound x).fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_of_le_one_right (norm_nonneg _)
    (norm_gaussianScaling_le_one ⟨hr.1.le, hr.2.le⟩)).trans ?_
  simpa only [Fintype.card_fin] using
    norm_integral_gaussianProductDensityDerivative_smul_le hf hbound
      ⟨1 - r ^ 2, by nlinarith [hr.1, hr.2]⟩
      (show (⟨1 - r ^ 2, by nlinarith [hr.1, hr.2]⟩ : ℝ≥0) ≠ 0 by
        apply ne_of_gt; change 0 < 1 - r ^ 2; nlinarith [hr.1, hr.2])
      (fun i => r * x i)
/-- The first derivative of Gaussian smoothing of a function bounded by one
is globally Lipschitz, with constant at most `n² * 2/(1-r²)`.
[MN15, §2, bounded derivatives after regularization; nonoptimal explicit bound]

**Proof sketch.** The density derivative is Lipschitz by the product Hessian
bound. Correlation scaling contracts distances, and composition with that
scaling contracts the norm of the resulting linear functional. -/
lemma lipschitzWith_fderiv_gaussianNoise {n : ℕ} {r : ℝ}
    (hr : r ∈ Set.Ioo (-1 : ℝ) 1) {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hbound : ∀ z, |f z| ≤ 1) :
    LipschitzWith ((n : ℝ≥0) ^ 2 *
      (2 / ⟨1 - r ^ 2, by nlinarith [hr.1, hr.2]⟩))
      (fderiv ℝ (gaussianNoise r f)) := by
  classical
  let v : ℝ≥0 := ⟨1 - r ^ 2, by nlinarith [hr.1, hr.2]⟩
  have hv : v ≠ 0 := by
    apply ne_of_gt; change 0 < 1 - r ^ 2; nlinarith [hr.1, hr.2]
  let L := r • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  have hL : ‖L‖ ≤ 1 := norm_gaussianScaling_le_one ⟨hr.1.le, hr.2.le⟩
  let D (c : Fin n → ℝ) := ∫ z : Fin n → ℝ,
    f z • gaussianProductDensityDerivative v c z
      ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ))
  have hD : LipschitzWith ((n : ℝ≥0) ^ 2 * (2 / v)) D := by
    simpa only [Fintype.card_fin] using
      lipschitzWith_integral_gaussianProductDensityDerivative hf hbound v hv
  have heq : fderiv ℝ (gaussianNoise r f) = fun x => (D (L x)).comp L := by
    funext x
    exact (hasFDerivAt_gaussianNoise_density hr hf hbound x).fderiv
  rw [heq]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.sub_comp]
  have hpoint : ‖L x - L y‖ ≤ ‖x - y‖ := by
    rw [← map_sub]
    exact (L.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hL)
  calc
    _ ≤ ‖D (L x) - D (L y)‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖D (L x) - D (L y)‖ := mul_le_of_le_one_right (norm_nonneg _) hL
    _ ≤ _ := (hD.norm_sub_le _ _).trans
      (mul_le_mul_of_nonneg_left hpoint (NNReal.coe_nonneg _))
/-- The second derivative of Gaussian smoothing of a function bounded by
one is uniformly bounded by `n² * 2/(1-r²)`.
[MN15, §2, bounded derivatives after regularization; nonoptimal explicit bound] -/
lemma norm_fderiv_fderiv_gaussianNoise_le {n : ℕ} {r : ℝ}
    (hr : r ∈ Set.Ioo (-1 : ℝ) 1) {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hbound : ∀ z, |f z| ≤ 1) (x : Fin n → ℝ) :
    ‖fderiv ℝ (fderiv ℝ (gaussianNoise r f)) x‖ ≤
      (n : ℝ) ^ 2 * (2 / (1 - r ^ 2)) := by
  simpa only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
    NNReal.coe_mk, NNReal.coe_natCast] using
    norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_fderiv_gaussianNoise hr hf hbound)
end BooleanAnalysis.GaussianSpace
