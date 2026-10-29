/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Definitions
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Probability.Distributions.Gaussian.Real

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Differentiating Gaussian averages in the mean

## Main definitions

The existing real Gaussian density and Gaussian law are reused. Averages are
written as density integrals, with the variance fixed and nonzero.

## Main results

* Affine Gaussian indicator averages equal integrals against the affine law's
  density, including negative nonzero scales.
* The first two mean derivatives of the density admit integrable envelopes
  on every bounded set of means.
* A bounded measurable function's Gaussian average is continuously
  differentiable, with uniformly bounded and Lipschitz first derivative.

The explicit regularity constants are convenient nonsharp bounds. The density
comparison and absolute-integral bounds apply to the totalized integral;
regularity statements require measurable inputs and establish genuine
integrability using the envelopes before differentiating.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian smoothing, and §11.4,
  the smooth indicator approximation for Gaussian isoperimetry.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- An affine Gaussian average of a measurable indicator equals its integral against
the corresponding translated and scaled Gaussian density.
[OD14, §11.1; §11.4, Gaussian indicator smoothing]

**Proof sketch.** Push the standard Gaussian law through the affine map using
the existing Gaussian scaling and translation laws, then apply the existing
Gaussian density integral formula. -/
lemma integral_indicator_gaussian_affine {A : Set ℝ} (hA : MeasurableSet A)
    (c s : ℝ) (hs : s ≠ 0) :
    (∫ y : ℝ, A.indicator (fun _ => (1 : ℝ)) (c + s * y)
      ∂standardGaussianMeasure) =
      ∫ z : ℝ, gaussianPDFReal c ⟨s ^ 2, sq_nonneg s⟩ z *
        A.indicator (fun _ => (1 : ℝ)) z := by
  let v : ℝ≥0 := ⟨s ^ 2, sq_nonneg s⟩
  have hv : v ≠ 0 := by
    intro h
    have : s ^ 2 = 0 := congrArg Subtype.val h
    exact hs (eq_zero_of_pow_eq_zero this)
  have hmap : standardGaussianMeasure.map (fun y : ℝ => c + s * y) =
      gaussianReal c v := by
    rw [show (fun y : ℝ => c + s * y) =
        (fun z : ℝ => c + z) ∘ (fun y : ℝ => s * y) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), standardGaussianMeasure,
      gaussianReal_map_const_mul, gaussianReal_map_const_add]
    simp [v]
  calc
    (∫ y : ℝ, A.indicator (fun _ => (1 : ℝ)) (c + s * y)
        ∂standardGaussianMeasure) =
        ∫ z : ℝ, A.indicator (fun _ => (1 : ℝ)) z ∂gaussianReal c v := by
      rw [← hmap, integral_map (by fun_prop)
        ((measurable_const.indicator hA).aestronglyMeasurable)]
    _ = _ := by
      rw [integral_gaussianReal_eq_integral_smul hv]
      rfl

/-- Differentiation of a Gaussian density in its mean introduces its centered
linear factor divided by the variance. [OD14, §11.1; §11.4, Gaussian indicator smoothing] -/
lemma hasDerivAt_gaussianPDFReal_mean (c z : ℝ) (v : ℝ≥0) :
    HasDerivAt (fun m : ℝ => gaussianPDFReal m v z)
      ((z - c) / v * gaussianPDFReal c v z) c := by
  unfold gaussianPDFReal
  convert (((((hasDerivAt_const c z).sub (hasDerivAt_id c)).pow 2).neg.div_const
      (2 * (v : ℝ))).exp.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹) using 1
  simp only [Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, id_eq,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- Mean derivatives of Gaussian densities with bounded means admit one integrable
envelope. The envelope is a linear polynomial times a Gaussian with wider variance.
[OD14, §11.1; §11.4, Gaussian indicator smoothing]

**Proof sketch.** The inequality `(z-m)^2 ≥ z^2/2-m^2` bounds every translated
Gaussian by a fixed wider Gaussian. Bound the centered linear factor by
`|z|+M`, then use the existing zeroth and first Gaussian integrability results. -/
lemma gaussianPDFReal_meanDerivative_dominated (v : ℝ≥0) (hv : v ≠ 0)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ b : ℝ → ℝ, Integrable b ∧ ∀ m : ℝ, |m| ≤ M → ∀ z : ℝ,
      |(z - m) / v * gaussianPDFReal m v z| ≤ b z := by
  have hv' : 0 < (v : ℝ) := by positivity
  have hb : 0 < (4 * (v : ℝ))⁻¹ := by positivity
  let k : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ / v
  let C : ℝ := k * Real.exp (M ^ 2 / (2 * v))
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hbase : Integrable (fun z : ℝ =>
      (|z| + M) * Real.exp (-(4 * (v : ℝ))⁻¹ * z ^ 2)) := by
    convert ((integrable_mul_exp_neg_mul_sq hb).abs).add
      ((integrable_exp_neg_mul_sq hb).const_mul M) using 1
    funext z
    simp only [Pi.add_apply]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    ring
  refine ⟨fun z => C * ((|z| + M) * Real.exp (-(4 * (v : ℝ))⁻¹ * z ^ 2)),
    hbase.const_mul C, ?_⟩
  intro m hm z
  have hm2 : m ^ 2 ≤ M ^ 2 := by
    nlinarith [sq_abs m,
      mul_nonneg (sub_nonneg.mpr hm) (add_nonneg hM (abs_nonneg m))]
  have hnorm : |z - m| ≤ |z| + M :=
    (abs_sub z m).trans (add_le_add_left hm _)
  have hexp : Real.exp (-(z - m) ^ 2 / (2 * v)) ≤
      Real.exp (M ^ 2 / (2 * v)) * Real.exp (-(4 * (v : ℝ))⁻¹ * z ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hquad : -2 * (z - m) ^ 2 ≤ 2 * M ^ 2 - z ^ 2 := by
      nlinarith [sq_nonneg (z - 2 * m)]
    have h := div_le_div_of_nonneg_right hquad (show 0 ≤ 4 * (v : ℝ) by positivity)
    convert h using 1 <;> field_simp <;> ring
  calc
    |(z - m) / v * gaussianPDFReal m v z| =
        k * |z - m| * Real.exp (-(z - m) ^ 2 / (2 * v)) := by
      rw [abs_mul, abs_div, abs_of_pos hv',
        abs_of_nonneg (gaussianPDFReal_nonneg m v z), gaussianPDFReal]
      dsimp [k]
      ring
    _ ≤ k * (|z| + M) *
        (Real.exp (M ^ 2 / (2 * v)) * Real.exp (-(4 * (v : ℝ))⁻¹ * z ^ 2)) := by
      gcongr
    _ = _ := by dsimp [C]; ring

/-- Integrating a bounded measurable function against a Gaussian density is
differentiable in the mean, with the derivative obtained by differentiating the density.
[OD14, §11.1; §11.4, Gaussian indicator smoothing]

**Proof sketch.** Near the specified mean, the preceding envelope dominates the
density derivative. Multiplication by a function bounded by one preserves this
domination. Apply differentiation under the integral sign. -/
lemma hasDerivAt_integral_gaussianPDFReal_mean {f : ℝ → ℝ} (hf : Measurable f)
    (hfbound : ∀ z, |f z| ≤ 1) (v : ℝ≥0) (hv : v ≠ 0) (c : ℝ) :
    HasDerivAt (fun m : ℝ => ∫ z : ℝ, gaussianPDFReal m v z * f z)
      (∫ z : ℝ, ((z - c) / v * gaussianPDFReal c v z) * f z) c := by
  obtain ⟨b, hb, hbound⟩ := gaussianPDFReal_meanDerivative_dominated v hv
    (|c| + 1) (by positivity)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun m z : ℝ => gaussianPDFReal m v z * f z)
    (F' := fun m z : ℝ => ((z - m) / v * gaussianPDFReal m v z) * f z)
    (bound := b) (show (0 : ℝ) < 1 by norm_num)
    (Eventually.of_forall fun m =>
      ((measurable_gaussianPDFReal m v).mul hf).aestronglyMeasurable)
    ?_ ?_ ?_ hb ?_).2
  · refine (integrable_gaussianPDFReal c v).mono'
      ((measurable_gaussianPDFReal c v).mul hf).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg c v z)]
    exact mul_le_of_le_one_right (gaussianPDFReal_nonneg c v z) (hfbound z)
  · exact ((((measurable_id.sub_const c).div_const (v : ℝ)).mul
      (measurable_gaussianPDFReal c v)).mul hf).aestronglyMeasurable
  · filter_upwards [] with z m hm
    have hm' : |m| ≤ |c| + 1 := by
      have hmc : |m - c| < 1 := by
        simpa only [Metric.mem_ball, Real.dist_eq] using hm
      have htri := abs_add_le (m - c) c
      rw [sub_add_cancel] at htri
      linarith
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hfbound z)).trans (hbound m hm' z)
  · exact Eventually.of_forall fun z m _ =>
      (hasDerivAt_gaussianPDFReal_mean m z v).mul_const (f z)

/-- The second mean derivative of a Gaussian density is its centered quadratic
factor divided by the squared variance, minus the inverse variance. [OD14, §11.1; §11.4, Gaussian indicator smoothing] -/
lemma hasDerivAt_gaussianPDFReal_meanDerivative (c z : ℝ) (v : ℝ≥0) :
    HasDerivAt (fun m : ℝ => (z - m) / v * gaussianPDFReal m v z)
      (((z - c) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * gaussianPDFReal c v z) c := by
  convert ((((hasDerivAt_const c z).sub (hasDerivAt_id c)).div_const (v : ℝ)).mul
    (hasDerivAt_gaussianPDFReal_mean c z v)) using 1
  simp only [Pi.sub_apply, id_eq, div_eq_mul_inv]
  ring

/-- Second mean derivatives of Gaussian densities with bounded means admit one
integrable envelope, given by a quadratic polynomial times a wider Gaussian.
[OD14, §11.1; §11.4, Gaussian indicator smoothing]

**Proof sketch.** Bound the centered quadratic factor by a fixed quadratic in
the integration variable. The same translated-Gaussian estimate as for the first
derivative bounds the exponential factor. Gaussian integrability with powers
zero and two proves integrability of the resulting envelope. -/
lemma gaussianPDFReal_secondMeanDerivative_dominated (v : ℝ≥0) (hv : v ≠ 0)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ b : ℝ → ℝ, Integrable b ∧ ∀ m : ℝ, |m| ≤ M → ∀ z : ℝ,
      |(((z - m) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * gaussianPDFReal m v z)| ≤ b z := by
  have hv' : 0 < (v : ℝ) := by positivity
  have hb : 0 < (4 * (v : ℝ))⁻¹ := by positivity
  let k : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹
  let C : ℝ := k * Real.exp (M ^ 2 / (2 * v))
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hz2 : Integrable (fun z : ℝ =>
      z ^ 2 * Real.exp (-(4 * (v : ℝ))⁻¹ * z ^ 2)) := by
    simpa only [Real.rpow_two] using
      integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)
  have hbase : Integrable (fun z : ℝ =>
      (2 * (z ^ 2 + M ^ 2) / (v : ℝ) ^ 2 + 1 / v) *
        Real.exp (-(4 * (v : ℝ))⁻¹ * z ^ 2)) := by
    convert (hz2.const_mul (2 / (v : ℝ) ^ 2)).add
      ((integrable_exp_neg_mul_sq hb).const_mul
        (2 * M ^ 2 / (v : ℝ) ^ 2 + 1 / v)) using 1
    funext z
    simp only [Pi.add_apply]
    ring
  refine ⟨fun z => C * ((2 * (z ^ 2 + M ^ 2) / (v : ℝ) ^ 2 + 1 / v) *
    Real.exp (-(4 * (v : ℝ))⁻¹ * z ^ 2)), hbase.const_mul C, ?_⟩
  intro m hm z
  have hm2 : m ^ 2 ≤ M ^ 2 := by
    nlinarith [sq_abs m,
      mul_nonneg (sub_nonneg.mpr hm) (add_nonneg hM (abs_nonneg m))]
  have hpoly : |(z - m) ^ 2 / (v : ℝ) ^ 2 - 1 / v| ≤
      2 * (z ^ 2 + M ^ 2) / (v : ℝ) ^ 2 + 1 / v := by
    calc
      _ ≤ |(z - m) ^ 2 / (v : ℝ) ^ 2| + |1 / (v : ℝ)| := abs_sub _ _
      _ = (z - m) ^ 2 / (v : ℝ) ^ 2 + 1 / v := by
        rw [abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
      _ ≤ _ := by
        gcongr
        nlinarith [sq_nonneg (z + m)]
  have hexp : Real.exp (-(z - m) ^ 2 / (2 * v)) ≤
      Real.exp (M ^ 2 / (2 * v)) * Real.exp (-(4 * (v : ℝ))⁻¹ * z ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hquad : -2 * (z - m) ^ 2 ≤ 2 * M ^ 2 - z ^ 2 := by
      nlinarith [sq_nonneg (z - 2 * m)]
    have h := div_le_div_of_nonneg_right hquad (show 0 ≤ 4 * (v : ℝ) by positivity)
    convert h using 1 <;> field_simp <;> ring
  rw [abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg m v z), gaussianPDFReal]
  calc
    _ = k * |(z - m) ^ 2 / (v : ℝ) ^ 2 - 1 / v| *
        Real.exp (-(z - m) ^ 2 / (2 * v)) := by dsimp [k]; ring
    _ ≤ k * (2 * (z ^ 2 + M ^ 2) / (v : ℝ) ^ 2 + 1 / v) *
        (Real.exp (M ^ 2 / (2 * v)) * Real.exp (-(4 * (v : ℝ))⁻¹ * z ^ 2)) := by
      gcongr
    _ = _ := by dsimp [C]; ring

/-- The mean derivative of a bounded Gaussian average is differentiable once more,
with the quadratic Gaussian kernel as its derivative.
[OD14, §11.1; §11.4, Gaussian indicator smoothing]

**Proof sketch.** Use the first derivative envelope for integrability at the
specified mean and the second derivative envelope for local domination. Then
apply differentiation under the integral sign a second time. -/
lemma hasDerivAt_integral_gaussianPDFReal_meanDerivative {f : ℝ → ℝ}
    (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) (c : ℝ) :
    HasDerivAt (fun m : ℝ => ∫ z : ℝ, ((z - m) / v * gaussianPDFReal m v z) * f z)
      (∫ z : ℝ, (((z - c) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * gaussianPDFReal c v z) * f z)
      c := by
  obtain ⟨b, hb, hbound⟩ := gaussianPDFReal_secondMeanDerivative_dominated v hv
    (|c| + 1) (by positivity)
  obtain ⟨a, ha, habound⟩ := gaussianPDFReal_meanDerivative_dominated v hv
    (|c|) (abs_nonneg c)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun m z : ℝ => ((z - m) / v * gaussianPDFReal m v z) * f z)
    (F' := fun m z : ℝ =>
      (((z - m) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * gaussianPDFReal m v z) * f z)
    (bound := b) (show (0 : ℝ) < 1 by norm_num)
    (Eventually.of_forall fun m =>
      ((((measurable_id.sub_const m).div_const (v : ℝ)).mul
        (measurable_gaussianPDFReal m v)).mul hf).aestronglyMeasurable)
    ?_ ?_ ?_ hb ?_).2
  · refine ha.mono'
      ((((measurable_id.sub_const c).div_const (v : ℝ)).mul
        (measurable_gaussianPDFReal c v)).mul hf).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hfbound z)).trans
      (habound c le_rfl z)
  · exact ((((((measurable_id.sub_const c).pow_const 2).div_const ((v : ℝ) ^ 2)).sub_const
      (1 / (v : ℝ))).mul (measurable_gaussianPDFReal c v)).mul hf).aestronglyMeasurable
  · filter_upwards [] with z m hm
    have hm' : |m| ≤ |c| + 1 := by
      have hmc : |m - c| < 1 := by
        simpa only [Metric.mem_ball, Real.dist_eq] using hm
      have htri := abs_add_le (m - c) c
      rw [sub_add_cancel] at htri
      linarith
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hfbound z)).trans (hbound m hm' z)
  · exact Eventually.of_forall fun z m _ =>
      (hasDerivAt_gaussianPDFReal_meanDerivative m z v).mul_const (f z)

/-- The centered second moment of a real Gaussian law equals its variance
parameter, including zero variance. [OD14, §11.1, Gaussian moments]

**Proof sketch.** Expand Mathlib's Gaussian variance identity as the integral
of the centered square and substitute its Gaussian mean formula. -/
lemma integral_centered_sq_gaussianReal (c : ℝ) (v : ℝ≥0) :
    (∫ z : ℝ, (z - c) ^ 2 ∂gaussianReal c v) = v := by
  have h := variance_fun_id_gaussianReal (μ := c) (v := v)
  rw [variance_eq_integral (X := fun z : ℝ => z) measurable_id.aemeasurable] at h
  simpa only [integral_id_gaussianReal] using h

/-- A pointwise absolute bound under a Gaussian law also bounds the absolute
Lebesgue integral against its density. [OD14, §11.1; §11.4, Gaussian indicator smoothing] -/
lemma abs_integral_gaussianPDFReal_mul_le {g b : ℝ → ℝ} (v : ℝ≥0) (hv : v ≠ 0)
    (c : ℝ) (hb : Integrable b (gaussianReal c v)) (hbound : ∀ z, |g z| ≤ b z) :
    |∫ z : ℝ, gaussianPDFReal c v z * g z| ≤ ∫ z : ℝ, b z ∂gaussianReal c v := by
  change |∫ z : ℝ, gaussianPDFReal c v z • g z| ≤ ∫ z : ℝ, b z ∂gaussianReal c v
  rw [← integral_gaussianReal_eq_integral_smul hv]
  calc
    _ ≤ ∫ z : ℝ, |g z| ∂gaussianReal c v := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := gaussianReal c v) g
    _ ≤ _ := integral_mono_of_nonneg
      (Eventually.of_forall fun z => abs_nonneg (g z)) hb (Eventually.of_forall hbound)

/-- The absolute second mean derivative of a Gaussian average of a function
bounded by one is at most twice the inverse variance, independently of the mean.
[OD14, §11.1; §11.4, Gaussian indicator smoothing]

**Proof sketch.** Rewrite the density integral as an expectation under the
Gaussian law. Bound the absolute centered quadratic kernel by the sum of its
nonnegative terms, whose expectations are the variance and one. -/
lemma abs_integral_gaussianPDFReal_secondMeanDerivative_le {f : ℝ → ℝ}
    (hfbound : ∀ z, |f z| ≤ 1) (v : ℝ≥0) (hv : v ≠ 0) (c : ℝ) :
    |∫ z : ℝ, (((z - c) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * gaussianPDFReal c v z) * f z|
      ≤ 2 / (v : ℝ) := by
  have hv' : 0 < (v : ℝ) := by positivity
  have hi : Integrable (fun z : ℝ => (z - c) ^ 2) (gaussianReal c v) :=
    ((memLp_id_gaussianReal (μ := c) (v := v) 2).sub (memLp_const c)).integrable_sq
  have hmoment := integral_centered_sq_gaussianReal c v
  have hrewrite : (fun z : ℝ =>
      (((z - c) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * gaussianPDFReal c v z) * f z) =
      (fun z : ℝ => gaussianPDFReal c v z *
        (((z - c) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * f z)) := by
    funext z
    ring
  rw [hrewrite]
  change |∫ z : ℝ, gaussianPDFReal c v z •
    (((z - c) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * f z)| ≤ 2 / (v : ℝ)
  rw [← integral_gaussianReal_eq_integral_smul hv]
  calc
    _ ≤ ∫ z : ℝ, |((z - c) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * f z| ∂gaussianReal c v :=
      by simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := gaussianReal c v)
          (fun z : ℝ => ((z - c) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * f z)
    _ ≤ ∫ z : ℝ, ((z - c) ^ 2 / (v : ℝ) ^ 2 + 1 / v) ∂gaussianReal c v := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _)
        ((hi.div_const _).add (integrable_const _)) (Eventually.of_forall fun z => ?_)
      dsimp only
      rw [abs_mul]
      calc
        _ ≤ |(z - c) ^ 2 / (v : ℝ) ^ 2 - 1 / v| :=
          mul_le_of_le_one_right (abs_nonneg _) (hfbound z)
        _ ≤ _ := by
          convert abs_sub ((z - c) ^ 2 / (v : ℝ) ^ 2) (1 / (v : ℝ)) using 1
          rw [abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
    _ = 2 / (v : ℝ) := by
      rw [integral_add (hi.div_const _) (integrable_const _), integral_div,
        hmoment, integral_const]
      simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
      field_simp
      ring

/-- The absolute first mean derivative of a Gaussian average of a function
bounded by one is bounded uniformly in the mean. The bound is deliberately
nonsharp; its role is to provide a global regularity constant.
[OD14, §11.1; §11.4, Gaussian indicator smoothing]

**Proof sketch.** Under the Gaussian law, use the elementary inequality
`|z-c| ≤ (z-c)^2 + 1` and evaluate the centered second moment. -/
lemma abs_integral_gaussianPDFReal_meanDerivative_le {f : ℝ → ℝ}
    (hfbound : ∀ z, |f z| ≤ 1) (v : ℝ≥0) (hv : v ≠ 0) (c : ℝ) :
    |∫ z : ℝ, ((z - c) / v * gaussianPDFReal c v z) * f z| ≤ 1 + 1 / (v : ℝ) := by
  have hv' : 0 < (v : ℝ) := by positivity
  have hi : Integrable (fun z : ℝ => (z - c) ^ 2) (gaussianReal c v) :=
    ((memLp_id_gaussianReal (μ := c) (v := v) 2).sub (memLp_const c)).integrable_sq
  have hmoment := integral_centered_sq_gaussianReal c v
  have hrewrite : (fun z : ℝ => ((z - c) / v * gaussianPDFReal c v z) * f z) =
      (fun z : ℝ => gaussianPDFReal c v z * ((z - c) / v * f z)) := by
    funext z
    ring
  rw [hrewrite]
  calc
    _ ≤ ∫ z : ℝ, ((z - c) ^ 2 + 1) / (v : ℝ) ∂gaussianReal c v := by
      apply abs_integral_gaussianPDFReal_mul_le v hv c ((hi.add (integrable_const _)).div_const _)
      intro z
      rw [abs_mul, abs_div, abs_of_pos hv']
      calc
        _ ≤ |z - c| / (v : ℝ) :=
          mul_le_of_le_one_right (by positivity) (hfbound z)
        _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ hv'.le
          change |z - c| ≤ (z - c) ^ 2 + 1
          nlinarith [sq_nonneg (|z - c| - 1 / 2), sq_abs (z - c)]
    _ = 1 + 1 / (v : ℝ) := by
      rw [integral_div, integral_add hi (integrable_const _), hmoment, integral_const]
      simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
      field_simp

/-- The first mean derivative of a Gaussian average of a measurable function
bounded by one is globally Lipschitz, with constant twice the inverse variance. [OD14, §11.1; §11.4, Gaussian indicator smoothing] -/
lemma lipschitzWith_integral_gaussianPDFReal_meanDerivative {f : ℝ → ℝ}
    (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) :
    LipschitzWith (2 / v) (fun c : ℝ =>
      ∫ z : ℝ, ((z - c) / v * gaussianPDFReal c v z) * f z) := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun c => (hasDerivAt_integral_gaussianPDFReal_meanDerivative hf hfbound v hv c).differentiableAt)
    (fun c => ?_)
  change ‖deriv (fun m : ℝ =>
    ∫ z : ℝ, ((z - m) / v * gaussianPDFReal m v z) * f z) c‖ ≤ (2 / v : ℝ≥0)
  rw [(hasDerivAt_integral_gaussianPDFReal_meanDerivative hf hfbound v hv c).deriv,
    Real.norm_eq_abs]
  exact abs_integral_gaussianPDFReal_secondMeanDerivative_le hfbound v hv c

/-- A Gaussian average of a measurable function bounded by one is globally
Lipschitz in its mean, with an explicit finite regularity constant. [OD14, §11.1; §11.4, Gaussian indicator smoothing] -/
lemma lipschitzWith_integral_gaussianPDFReal_mean {f : ℝ → ℝ}
    (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1) (v : ℝ≥0) (hv : v ≠ 0) :
    LipschitzWith (1 + 1 / v) (fun c : ℝ => ∫ z : ℝ, gaussianPDFReal c v z * f z) := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun c => (hasDerivAt_integral_gaussianPDFReal_mean hf hfbound v hv c).differentiableAt)
    (fun c => ?_)
  change ‖deriv (fun m : ℝ => ∫ z : ℝ, gaussianPDFReal m v z * f z) c‖ ≤
    (1 + 1 / v : ℝ≥0)
  rw [(hasDerivAt_integral_gaussianPDFReal_mean hf hfbound v hv c).deriv, Real.norm_eq_abs]
  exact abs_integral_gaussianPDFReal_meanDerivative_le hfbound v hv c

/-- A Gaussian average of a bounded measurable function is continuously
differentiable in its mean. [OD14, §11.1; §11.4, Gaussian indicator smoothing] -/
lemma contDiff_one_integral_gaussianPDFReal_mean {f : ℝ → ℝ}
    (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1) (v : ℝ≥0) (hv : v ≠ 0) :
    ContDiff ℝ 1 (fun m : ℝ => ∫ z : ℝ, gaussianPDFReal m v z * f z) := by
  refine contDiff_one_iff_deriv.mpr ⟨fun c =>
    (hasDerivAt_integral_gaussianPDFReal_mean hf hfbound v hv c).differentiableAt, ?_⟩
  have hderiv : deriv (fun m : ℝ => ∫ z : ℝ, gaussianPDFReal m v z * f z) =
      (fun m : ℝ => ∫ z : ℝ, ((z - m) / v * gaussianPDFReal m v z) * f z) :=
    funext fun m => (hasDerivAt_integral_gaussianPDFReal_mean hf hfbound v hv m).deriv
  rw [hderiv]
  exact (lipschitzWith_integral_gaussianPDFReal_meanDerivative hf hfbound v hv).continuous

end BooleanAnalysis.GaussianSpace
