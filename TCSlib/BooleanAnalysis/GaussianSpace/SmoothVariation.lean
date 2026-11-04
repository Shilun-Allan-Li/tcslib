/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Halfspace
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Smooth Gaussian rotation variation and gradient bounds

## Main definitions

The existing derivative and canonical basis are used for gradient lengths.
No separate differentiability or perimeter representation is introduced.

## Main results

* Rotation difference quotients tend to Gaussian directional derivatives.
* Gaussian directional integration gives the Euclidean gradient length.
* Fatou's inequality bounds the integral gradient length by every uniform
  bound on normalized integral rotation variation.

Nonnegative extended integrals keep these bounds valid for infinite variation.
The real-integral adapter explicitly proves integrability for unit-interval
functions before identifying it with the corresponding nonnegative integral.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian linear projections, and §11.4,
  Definition 11.48 and the smooth surface-area argument.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- A differentiable real function restricted to the Gaussian rotation curve has
derivative equal to its derivative applied to the second endpoint at angle zero.
[OD14, §11.4, Def. 11.48]

**Proof sketch.** The rotation curve starts at x and has velocity y at zero;
apply the chain rule. -/
lemma hasDerivAt_gaussianRotation_comp {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} {L : (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f L x) (y : Fin n → ℝ) :
    HasDerivAt (fun θ : ℝ => f (fun i => Real.cos θ * x i + Real.sin θ * y i))
      (L y) 0 := by
  have hcurve : HasDerivAt
      (fun θ : ℝ => fun i => Real.cos θ * x i + Real.sin θ * y i) y 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa using ((Real.hasDerivAt_cos 0).mul_const (x i)).add
      ((Real.hasDerivAt_sin 0).mul_const (y i))
  have hf' : HasFDerivAt f L (fun i => Real.cos 0 * x i + Real.sin 0 * y i) := by
    simpa using hf
  exact hf'.comp_hasDerivAt 0 hcurve

/-- The positive-angle absolute rotation difference quotient converges to the
absolute directional derivative. [OD14, §11.4, Def. 11.48]

**Proof sketch.** Take absolute values in the derivative limit. The angle is
positive, so its absolute value equals the angle itself. -/
lemma gaussianRotation_difference_quotient_tendsto {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    {L : (Fin n → ℝ) →L[ℝ] ℝ} (hf : HasFDerivAt f L x) (y : Fin n → ℝ) :
    Tendsto (fun θ : ℝ =>
      |f (fun i => Real.cos θ * x i + Real.sin θ * y i) - f x| / θ)
      (𝓝[>] (0 : ℝ)) (𝓝 |L y|) := by
  have h := (hasDerivAt_gaussianRotation_comp hf y).tendsto_slope_zero_right.abs
  simp only [zero_add, Real.cos_zero, one_mul, Real.sin_zero, zero_mul,
    add_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  change 0 < θ at hθ
  simp [abs_of_pos hθ, div_eq_mul_inv, mul_comm]

/-- The first absolute Gaussian moment of a linear functional equals the Euclidean
length of its canonical-basis coefficients times the scalar absolute moment.
[OD14, §11.1, Gaussian linear projections]

**Proof sketch.** Expand the linear map in the canonical basis and apply the
absolute Gaussian projection moment formula. -/
lemma integral_abs_gaussianLinearMap {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] ℝ) :
    (∫ z : Fin n → ℝ, |L z|
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) =
      Real.sqrt (∑ i : Fin n, (L (Pi.single i 1)) ^ 2) *
        (2 * standardGaussianPDF 0) := by
  classical
  convert integral_abs_gaussianProjection (fun i : Fin n => L (Pi.single i 1)) using 1
  congr 1
  funext z
  congr 1
  have h := L.toLinearMap.pi_apply_eq_sum_univ z
  have hb (i : Fin n) : (fun j : Fin n => if i = j then (1 : ℝ) else 0) =
      Pi.single i 1 := by
    ext j
    simp [Pi.single_apply, eq_comm]
  simpa only [smul_eq_mul, hb, mul_comm] using h

/-- A bound on all positive-angle rotation difference quotients bounds the
nonnegative integral of the absolute directional derivative.
[OD14, §11.4, smooth surface-area argument]
The bound may be infinite; derivative integrability is not assumed.

**Proof sketch.** Take angles one divided by k+1. Their pointwise difference
quotients tend to the absolute directional derivative. Fatou's inequality
bounds its integral by the lower limit of the bounded quotient integrals. -/
lemma lintegral_gaussianRotation_derivative_le {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {L : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (L x) x) (C : ℝ≥0∞)
    (hbound : ∀ θ : ℝ, 0 < θ →
      (∫⁻ z : (Fin n → ℝ) × (Fin n → ℝ), ENNReal.ofReal
        (|f (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) - f z.1| / θ)
        ∂((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
          (Measure.pi fun _ : Fin n => standardGaussianMeasure))) ≤ C) :
    (∫⁻ z : (Fin n → ℝ) × (Fin n → ℝ), ENNReal.ofReal |L z.1 z.2|
      ∂((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure))) ≤ C := by
  let μ := (Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
    (Measure.pi fun _ : Fin n => standardGaussianMeasure)
  let t (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  let q (k : ℕ) (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ≥0∞ := ENNReal.ofReal
    (|f (fun i => Real.cos (t k) * z.1 i + Real.sin (t k) * z.2 i) - f z.1| / t k)
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have ht : Tendsto t atTop (𝓝[>] (0 : ℝ)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => by change 0 < 1 / ((k : ℝ) + 1); positivity⟩
  have hlim (z : (Fin n → ℝ) × (Fin n → ℝ)) :
      Tendsto (fun k => q k z) atTop (𝓝 (ENNReal.ofReal |L z.1 z.2|)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      ((gaussianRotation_difference_quotient_tendsto (hf z.1) z.2).comp ht)
  calc
    _ = ∫⁻ z, liminf (fun k => q k z) atTop ∂μ := by
      apply lintegral_congr
      intro z
      exact (hlim z).liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ z, q k z ∂μ) atTop :=
      lintegral_liminf_le (fun k => by dsimp [q]; fun_prop)
    _ ≤ liminf (fun _ : ℕ => C) atTop :=
      liminf_le_liminf (Eventually.of_forall fun k =>
        hbound (t k) (by dsimp [t]; positivity))
    _ = C := liminf_const C

/-- Every real continuous linear functional on a finite product of standard
Gaussians is integrable. [OD14, §11.1, Gaussian linear projections]

**Proof sketch.** Each coordinate has a finite first Gaussian moment. Express
the functional as their finite linear combination. -/
lemma integrable_gaussianLinearMap {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) :
    Integrable L (Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  classical
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  have hid : Integrable (id : ℝ → ℝ) standardGaussianMeasure :=
    memLp_one_iff_integrable.mp
      (ProbabilityTheory.memLp_id_gaussianReal' 1 (by norm_num))
  have hcoord (i : Fin n) : Integrable (fun z : Fin n → ℝ => z i)
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) :=
    (measurePreserving_eval (fun _ : Fin n => standardGaussianMeasure) i).integrable_comp_of_integrable hid
  have hsum := integrable_finset_sum Finset.univ
    (fun i _ => (hcoord i).mul_const (L (fun j => if i = j then 1 else 0)))
  convert hsum using 1
  funext z
  simpa only [smul_eq_mul] using L.toLinearMap.pi_apply_eq_sum_univ z

/-- The nonnegative integral of the absolute value of a Gaussian linear
functional is the nonnegative real embedding of its absolute-moment formula.
[OD14, §11.1, Gaussian linear projections]

**Proof sketch.** Its genuine integrability identifies the nonnegative integral
with the real integral, whose value was computed above. -/
lemma lintegral_abs_gaussianLinearMap {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] ℝ) :
    (∫⁻ z : Fin n → ℝ, ENNReal.ofReal |L z|
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) =
      ENNReal.ofReal (Real.sqrt (∑ i : Fin n, (L (Pi.single i 1)) ^ 2) *
        (2 * standardGaussianPDF 0)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianLinearMap L).abs
    (Eventually.of_forall fun z => abs_nonneg _), integral_abs_gaussianLinearMap]

/-- For a continuous family of linear functionals, averaging the absolute
Gaussian directional value gives the integral Euclidean coefficient length
times the scalar absolute Gaussian moment. [OD14, §11.4, smooth surface-area argument]

**Proof sketch.** Apply Tonelli to integrate first in the direction. The
Gaussian projection formula computes that inner integral, and its constant
factor comes outside the remaining nonnegative integral. -/
lemma lintegral_gaussianLinearMap_family {n : ℕ}
    (L : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) (hL : Continuous L) :
    (∫⁻ z : (Fin n → ℝ) × (Fin n → ℝ), ENNReal.ofReal |L z.1 z.2|
      ∂((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure))) =
      (∫⁻ x : Fin n → ℝ,
        ENNReal.ofReal (Real.sqrt (∑ i : Fin n, (L x (Pi.single i 1)) ^ 2))
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) *
        ENNReal.ofReal (2 * standardGaussianPDF 0) := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  rw [lintegral_prod _ (by fun_prop)]
  simp_rw [lintegral_abs_gaussianLinearMap,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top

/-- A bound on all rotation quotients normalized by sqrt(pi/2) bounds the
nonnegative integral of the Euclidean gradient length.
[OD14, §11.4, Def. 11.48 and smooth surface-area argument]
The gradient is expressed using any continuous family witnessing the derivative.

**Proof sketch.** Apply the directional Fatou bound to the function scaled by
sqrt(pi/2). Integrating the Gaussian direction gives the Euclidean gradient
length times its scalar absolute moment. The normalization cancels that moment
exactly. All integrals in this argument are nonnegative and may be infinite. -/
lemma lintegral_gaussianGradient_le {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {L : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (L x) x) (hL : Continuous L) (C : ℝ≥0∞)
    (hbound : ∀ θ : ℝ, 0 < θ →
      (∫⁻ z : (Fin n → ℝ) × (Fin n → ℝ), ENNReal.ofReal
        (Real.sqrt (Real.pi / 2) *
          |f (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) - f z.1| / θ)
        ∂((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
          (Measure.pi fun _ : Fin n => standardGaussianMeasure))) ≤ C) :
    (∫⁻ x : Fin n → ℝ,
      ENNReal.ofReal (Real.sqrt (∑ i : Fin n, (L x (Pi.single i 1)) ^ 2))
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) ≤ C := by
  let k := Real.sqrt (Real.pi / 2)
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hfscaled (x) : HasFDerivAt (fun x => k * f x) (k • L x) x := by
    simpa only [smul_eq_mul] using (hf x).const_smul k
  have h := lintegral_gaussianRotation_derivative_le hfscaled C (fun θ hθ => by
    convert hbound θ hθ using 1
    apply lintegral_congr
    intro z
    congr 1
    rw [show k * f (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) - k * f z.1 =
      k * (f (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) - f z.1) by ring,
      abs_mul, abs_of_nonneg hk])
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hk] at h
  simp_rw [ENNReal.ofReal_mul hk] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_gaussianLinearMap_family L hL] at h
  have hkm : ENNReal.ofReal k * ENNReal.ofReal (2 * standardGaussianPDF 0) = 1 := by
    rw [← ENNReal.ofReal_mul hk]
    simp only [k, gaussian_surface_normalization, ENNReal.ofReal_one]
  rwa [mul_left_comm, hkm, mul_one] at h

/-- For a differentiable unit-interval-valued function with continuous derivative,
bounds on its real integral rotation variation imply the same bound on the
nonnegative integral of its Euclidean gradient length.
[OD14, §11.4, smooth surface-area argument]

**Proof sketch.** The rotation differences are measurable and bounded by one,
so they are genuinely integrable under the Gaussian probability law. Identify
the normalized nonnegative quotient integral with the nonnegative embedding
of its real integral, then apply the gradient Fatou bound. -/
lemma lintegral_gaussianGradient_le_of_integral_variation_le {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {L : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (L x) x) (hL : Continuous L)
    (hunit : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (C : ℝ≥0∞)
    (hbound : ∀ θ : ℝ, 0 < θ →
      ENNReal.ofReal (Real.sqrt (Real.pi / 2) *
        (∫ z : (Fin n → ℝ) × (Fin n → ℝ),
          |f (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) - f z.1|
          ∂((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
            (Measure.pi fun _ : Fin n => standardGaussianMeasure))) / θ) ≤ C) :
    (∫⁻ x : Fin n → ℝ,
      ENNReal.ofReal (Real.sqrt (∑ i : Fin n, (L x (Pi.single i 1)) ^ 2))
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) ≤ C := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  apply lintegral_gaussianGradient_le hf hL C
  intro θ hθ
  have hint : Integrable (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      |f (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i) - f z.1|)
      ((Measure.pi fun _ : Fin n => standardGaussianMeasure).prod
        (Measure.pi fun _ : Fin n => standardGaussianMeasure)) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [] with z
    simp only [Real.norm_eq_abs, abs_abs]
    apply abs_le.mpr
    have hx := hunit z.1
    have hy := hunit (fun i => Real.cos θ * z.1 i + Real.sin θ * z.2 i)
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hint.const_mul (Real.sqrt (Real.pi / 2))).div_const θ)
    (Eventually.of_forall fun z => by positivity), integral_div, integral_const_mul]
  exact hbound θ hθ

end BooleanAnalysis.GaussianSpace
