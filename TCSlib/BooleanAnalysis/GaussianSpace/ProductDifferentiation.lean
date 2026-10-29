/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.ProductDensity
import TCSlib.BooleanAnalysis.GaussianSpace.ProductBounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Differentiating finite-product Gaussian averages

## Main definitions

* `gaussianProductDensityDerivative`: the ordinary derivative in the mean
  vector of the existing product Gaussian density.

## Main results

* Local integrable envelopes control the density and its derivative uniformly
  on bounded mean vectors.
* A bounded measurable real function's product Gaussian average is continuously
  differentiable in the mean vector, with derivative given by density differentiation.
* Coordinate Gaussian moment estimates give a global bound on this derivative.

The scalar envelope results are reused coordinatewise and combined with
finite-product integration. Every differentiated integral has genuine local
integrability before the parametric differentiation theorem is applied.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian smoothing, and §11.4,
  the smooth indicator approximation for Gaussian isoperimetry.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- On a bounded set of means, a single nonnegative integrable function bounds
a Gaussian density and its first two mean derivatives.
[OD14, §11.1; §11.4, Gaussian indicator smoothing]

**Proof sketch.** Reuse the first and second derivative envelopes. The mean value
estimate bounds the density itself by its value at mean zero plus the bound on
the mean times the first derivative envelope. Add the three nonnegative bounds. -/
lemma gaussianPDFReal_two_derivatives_dominated (v : ℝ≥0) (hv : v ≠ 0)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ b : ℝ → ℝ, Integrable b ∧ (∀ z, 0 ≤ b z) ∧ ∀ m : ℝ, |m| ≤ M → ∀ z : ℝ,
      gaussianPDFReal m v z ≤ b z ∧
      |(z - m) / v * gaussianPDFReal m v z| ≤ b z ∧
      |((z - m) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * gaussianPDFReal m v z| ≤ b z := by
  obtain ⟨b₁, hb₁, h₁⟩ := gaussianPDFReal_meanDerivative_dominated v hv M hM
  obtain ⟨b₂, hb₂, h₂⟩ := gaussianPDFReal_secondMeanDerivative_dominated v hv M hM
  have h₁pos (z : ℝ) : 0 ≤ b₁ z :=
    (abs_nonneg _).trans (h₁ 0 (by simpa using hM) z)
  have h₂pos (z : ℝ) : 0 ≤ b₂ z :=
    (abs_nonneg _).trans (h₂ 0 (by simpa using hM) z)
  refine ⟨fun z => gaussianPDFReal 0 v z + (M + 1) * b₁ z + b₂ z,
    ((integrable_gaussianPDFReal 0 v).add (hb₁.const_mul (M + 1))).add hb₂,
    fun z => add_nonneg (add_nonneg (gaussianPDFReal_nonneg 0 v z)
      (mul_nonneg (by linarith) (h₁pos z))) (h₂pos z), ?_⟩
  intro m hm z
  have hpdf : gaussianPDFReal m v z ≤ gaussianPDFReal 0 v z + M * b₁ z := by
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun a (_ : a ∈ Set.Icc (-M) M) =>
        (hasDerivAt_gaussianPDFReal_mean a z v).hasDerivWithinAt)
      (fun a (ha : a ∈ Set.Icc (-M) M) =>
        by simpa only [Real.norm_eq_abs] using h₁ a (abs_le.mpr ha) z)
      (convex_Icc (-M) M) (show 0 ∈ Set.Icc (-M) M by constructor <;> linarith)
      (show m ∈ Set.Icc (-M) M from abs_le.mp hm)
    simp only [Real.norm_eq_abs, sub_zero] at hmv
    have hmprod := mul_le_mul_of_nonneg_left hm (h₁pos z)
    have hsub := le_abs_self (gaussianPDFReal m v z - gaussianPDFReal 0 v z)
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [h₁pos z, h₂pos z]
  · have h := h₁ m hm z
    nlinarith [h₁pos z, h₂pos z, gaussianPDFReal_nonneg 0 v z]
  · have h := h₂ m hm z
    nlinarith [h₁pos z, h₂pos z, gaussianPDFReal_nonneg 0 v z]

/-- The derivative in the mean vector of the product Gaussian density,
written as its sum of coordinate derivatives. [OD14, §11.1; §11.4, Gaussian indicator smoothing] -/
noncomputable def gaussianProductDensityDerivative {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : ℝ≥0) (c z : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, ((∏ j ∈ Finset.univ.erase i, gaussianPDFReal (c j) v (z j)) *
    ((z i - c i) / v * gaussianPDFReal (c i) v (z i))) •
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)

/-- The product-density derivative is the density times the linear score
whose coordinate coefficients are the centered coordinates divided by the
variance parameter. [OD14, §11.1, Gaussian differentiation]

**Proof sketch.** In each coordinate term, the product of the remaining
densities times that coordinate's density is the full product density.
Factor this common scalar out of the finite sum of coordinate maps. -/
lemma gaussianProductDensityDerivative_eq_density_smul_score {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : ℝ≥0) (c z : ι → ℝ) :
    gaussianProductDensityDerivative v c z =
      (∏ i, gaussianPDFReal (c i) v (z i)) •
        (∑ i, ((z i - c i) / v) •
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) := by
  rw [gaussianProductDensityDerivative, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul]
  congr 1
  rw [← Finset.prod_erase_mul Finset.univ (fun j => gaussianPDFReal (c j) v (z j)) hi]
  ring

/-- Differentiating the product Gaussian density in its vector of means gives
the sum of its coordinate mean derivatives. [OD14, §11.1; §11.4, Gaussian indicator smoothing] -/
lemma hasFDerivAt_gaussianProductDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ℝ≥0) (c z : ι → ℝ) :
    HasFDerivAt (fun m : ι → ℝ => ∏ i, gaussianPDFReal (m i) v (z i))
      (gaussianProductDensityDerivative v c z) c := by
  have h (i : ι) : HasFDerivAt (fun m : ι → ℝ => gaussianPDFReal (m i) v (z i))
      (((z i - c i) / v * gaussianPDFReal (c i) v (z i)) •
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) c :=
    (hasDerivAt_gaussianPDFReal_mean (c i) (z i) v).comp_hasFDerivAt (f := fun m : ι → ℝ => m i) c
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt
  simpa only [gaussianProductDensityDerivative, smul_smul] using
    HasFDerivAt.finset_prod (u := Finset.univ) (fun i _ => h i)

/-- On a bounded set of mean vectors, the product Gaussian density and its
Fréchet derivative admit a common nonnegative integrable envelope.
[OD14, §11.1; §11.4, Gaussian indicator smoothing]

**Proof sketch.** Use the common scalar envelope in every coordinate. Each term
of the product derivative is bounded by the product of the scalar envelopes,
since coordinate projections have operator norm at most one. Sum over coordinates. -/
lemma gaussianProductDensity_derivative_dominated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ℝ≥0) (hv : v ≠ 0) (M : ℝ) (hM : 0 ≤ M) :
    ∃ b : (ι → ℝ) → ℝ,
      Integrable b (Measure.pi fun _ : ι => (volume : Measure ℝ)) ∧
      (∀ z, 0 ≤ b z) ∧ ∀ m : ι → ℝ, (∀ i, |m i| ≤ M) → ∀ z : ι → ℝ,
      |∏ i, gaussianPDFReal (m i) v (z i)| ≤ b z ∧
      ‖gaussianProductDensityDerivative v m z‖ ≤ b z := by
  obtain ⟨a, ha, hapos, habound⟩ := gaussianPDFReal_two_derivatives_dominated v hv M hM
  have haint : Integrable (fun z : ι → ℝ => ∏ i, a (z i))
      (Measure.pi fun _ : ι => (volume : Measure ℝ)) := Integrable.fintype_prod fun _ => ha
  refine ⟨fun z => (Fintype.card ι + 1 : ℝ) * ∏ i, a (z i),
    haint.const_mul _, fun z => mul_nonneg (by positivity)
      (Finset.prod_nonneg fun i _ => hapos (z i)), ?_⟩
  intro m hm z
  have hprod : 0 ≤ ∏ i, a (z i) := Finset.prod_nonneg fun i _ => hapos (z i)
  have hterm (i : ι) :
      ‖((∏ j ∈ Finset.univ.erase i, gaussianPDFReal (m j) v (z j)) *
          ((z i - m i) / v * gaussianPDFReal (m i) v (z i))) •
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ ∏ j, a (z j) := by
    have hproj := norm_coordinateProjection_le_one i
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |(∏ j ∈ Finset.univ.erase i, gaussianPDFReal (m j) v (z j)) *
          ((z i - m i) / v * gaussianPDFReal (m i) v (z i))| :=
        mul_le_of_le_one_right (abs_nonneg _) hproj
      _ = (∏ j ∈ Finset.univ.erase i, gaussianPDFReal (m j) v (z j)) *
          |(z i - m i) / v * gaussianPDFReal (m i) v (z i)| := by
        rw [abs_mul, abs_of_nonneg
          (Finset.prod_nonneg fun j _ => gaussianPDFReal_nonneg _ _ _)]
      _ ≤ (∏ j ∈ Finset.univ.erase i, a (z j)) * a (z i) := by
        apply mul_le_mul
        · exact Finset.prod_le_prod (fun j _ => gaussianPDFReal_nonneg _ _ _)
            (fun j _ => (habound (m j) (hm j) (z j)).1)
        · exact (habound (m i) (hm i) (z i)).2.1
        · exact abs_nonneg _
        · exact Finset.prod_nonneg fun j _ => hapos (z j)
      _ = ∏ j, a (z j) := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  constructor
  · rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _)]
    have h : (∏ i, gaussianPDFReal (m i) v (z i)) ≤ ∏ i, a (z i) :=
      Finset.prod_le_prod (fun i _ => gaussianPDFReal_nonneg _ _ _)
      (fun i _ => (habound (m i) (hm i) (z i)).1)
    nlinarith [mul_nonneg (show 0 ≤ (Fintype.card ι : ℝ) by positivity) hprod]
  · have hnorm : ‖gaussianProductDensityDerivative v m z‖ ≤
        Fintype.card ι * ∏ j, a (z j) := by
      calc
        _ ≤ ∑ i : ι, ∏ j, a (z j) := norm_sum_le_of_le _ (fun i _ => hterm i)
        _ = _ := by simp
    nlinarith

/-- The product-density derivative depends continuously jointly on the mean
and integration vectors. [OD14, §11.1; §11.4, Gaussian indicator smoothing] -/
lemma continuous_gaussianProductDensityDerivative_joint {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : ℝ≥0) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => gaussianProductDensityDerivative v p.1 p.2) := by
  unfold gaussianProductDensityDerivative gaussianPDFReal
  fun_prop

/-- The product-density derivative depends continuously on its integration vector. [OD14, §11.1; §11.4, Gaussian indicator smoothing] -/
lemma continuous_gaussianProductDensityDerivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ℝ≥0) (c : ι → ℝ) : Continuous (gaussianProductDensityDerivative v c) := by
  unfold gaussianProductDensityDerivative gaussianPDFReal
  fun_prop

/-- A bounded measurable multiplier preserves integrability of the
product Gaussian density derivative. [OD14, §11.1; §11.4, Gaussian indicator smoothing] -/
lemma integrable_gaussianProductDensityDerivative_smul {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) (c : ι → ℝ) :
    Integrable (fun z : ι → ℝ => f z • gaussianProductDensityDerivative v c z)
      (Measure.pi fun _ : ι => (volume : Measure ℝ)) := by
  obtain ⟨b, hb, _, hbound⟩ := gaussianProductDensity_derivative_dominated (ι := ι) v hv
    ‖c‖ (norm_nonneg c)
  refine hb.mono' (hf.smul (continuous_gaussianProductDensityDerivative v c).measurable).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hfbound z)).trans
    (hbound c (fun i => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c i) z).2

/-- A norm ball controls every coordinate by the center norm plus its radius. [OD14, §11.1; §11.4, Gaussian indicator smoothing] -/
lemma abs_coordinate_le_of_mem_ball {ι : Type*} [Fintype ι]
    {c m : ι → ℝ} {ε : ℝ} (hm : m ∈ Metric.ball c ε) (i : ι) :
    |m i| ≤ ‖c‖ + ε := by
  have hmc : ‖m - c‖ < ε := by simpa only [Metric.mem_ball, dist_eq_norm] using hm
  have htri : ‖m‖ ≤ ‖m - c‖ + ‖c‖ := by
    simpa only [sub_add_cancel] using norm_add_le (m - c) c
  have hcoord : |m i| ≤ ‖m‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm m i
  linarith

/-- The Gaussian average of a bounded measurable function is Fréchet
differentiable in its vector of means, and its derivative is the integral of
the product-density derivative.
[OD14, §11.1; §11.4, Gaussian indicator smoothing]

**Proof sketch.** Near the specified vector of means, the common product envelope
dominates the density and derivative. Multiplication by the bounded function
preserves these bounds. Differentiate under the integral sign. -/
lemma hasFDerivAt_integral_gaussianProductDensity {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) (c : ι → ℝ) :
    HasFDerivAt (fun m : ι → ℝ =>
      ∫ z : ι → ℝ, (∏ i, gaussianPDFReal (m i) v (z i)) * f z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ)))
      (∫ z : ι → ℝ, f z • gaussianProductDensityDerivative v c z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ))) c := by
  obtain ⟨b, hb, _, hbound⟩ := gaussianProductDensity_derivative_dominated (ι := ι) v hv
    (‖c‖ + 1) (by positivity)
  have hmeas (m : ι → ℝ) : Measurable (fun z : ι → ℝ =>
      (∏ i, gaussianPDFReal (m i) v (z i)) * f z) :=
    (Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal (m i) v).comp (measurable_pi_apply i)).mul hf
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun m z : ι → ℝ => (∏ i, gaussianPDFReal (m i) v (z i)) * f z)
    (F' := fun m z : ι → ℝ => f z • gaussianProductDensityDerivative v m z)
    (bound := b) (show (0 : ℝ) < 1 by norm_num)
    (Eventually.of_forall fun m => (hmeas m).aestronglyMeasurable) ?_
    (hf.smul (continuous_gaussianProductDensityDerivative v c).measurable).aestronglyMeasurable
    ?_ hb ?_
  · refine hb.mono' (hmeas c).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hfbound z)).trans
      (hbound c (abs_coordinate_le_of_mem_ball (Metric.mem_ball_self (by norm_num))) z).1
  · filter_upwards [] with z m hm
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hfbound z)).trans
      (hbound m (abs_coordinate_le_of_mem_ball hm) z).2
  · exact Eventually.of_forall fun z m _ =>
      (hasFDerivAt_gaussianProductDensity v m z).mul_const (f z)

/-- The integral of the bounded multiplier times the product-density derivative
varies continuously with the vector of means.
[OD14, §11.1; §11.4, Gaussian indicator smoothing]

**Proof sketch.** The kernel derivative is jointly continuous. On a neighborhood
of any fixed mean vector, the common integrable envelope permits dominated
convergence. -/
lemma continuous_integral_gaussianProductDensityDerivative {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) :
    Continuous (fun c : ι → ℝ =>
      ∫ z : ι → ℝ, f z • gaussianProductDensityDerivative v c z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ))) := by
  refine continuous_iff_continuousAt.mpr fun c => ?_
  obtain ⟨b, hb, _, hbound⟩ := gaussianProductDensity_derivative_dominated (ι := ι) v hv
    (‖c‖ + 1) (by positivity)
  refine continuousAt_of_dominated
    (Eventually.of_forall fun m =>
      (hf.smul (continuous_gaussianProductDensityDerivative v m).measurable).aestronglyMeasurable)
    ?_ hb ?_
  · filter_upwards [Metric.ball_mem_nhds c (show (0 : ℝ) < 1 by norm_num)] with m hm
    filter_upwards [] with z
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hfbound z)).trans
      (hbound m (abs_coordinate_le_of_mem_ball hm) z).2
  · exact Eventually.of_forall fun z =>
      (((continuous_gaussianProductDensityDerivative_joint v).comp
        (continuous_id.prodMk continuous_const)).const_smul (f z)).continuousAt

/-- A Gaussian average of a bounded measurable function is continuously
Fréchet differentiable in its vector of means. [OD14, §11.1; §11.4, Gaussian indicator smoothing] -/
lemma contDiff_one_integral_gaussianProductDensity {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) :
    ContDiff ℝ 1 (fun m : ι → ℝ =>
      ∫ z : ι → ℝ, (∏ i, gaussianPDFReal (m i) v (z i)) * f z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ))) := by
  refine contDiff_one_iff_fderiv.mpr ⟨fun c =>
    (hasFDerivAt_integral_gaussianProductDensity hf hfbound v hv c).differentiableAt, ?_⟩
  have hderiv : fderiv ℝ (fun m : ι → ℝ =>
      ∫ z : ι → ℝ, (∏ i, gaussianPDFReal (m i) v (z i)) * f z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ))) =
      (fun c : ι → ℝ => ∫ z : ι → ℝ, f z • gaussianProductDensityDerivative v c z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ))) :=
    funext fun c => (hasFDerivAt_integral_gaussianProductDensity hf hfbound v hv c).fderiv
  rw [hderiv]
  exact continuous_integral_gaussianProductDensityDerivative hf hfbound v hv

/-- The derivative integral of a bounded measurable Gaussian average equals
the sum of its coordinate-score expectations times the coordinate projections.
[OD14, §11.1; §11.4, Gaussian smoothing]

**Proof sketch.** Factor the product density out of its derivative and move
to the Gaussian product law. Each coordinate score times the multiplier is
genuinely integrable, so the finite sum and scalar projections commute with
integration. -/
lemma integral_gaussianProductDensityDerivative_smul_eq_sum {ι : Type*}
    [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) (c : ι → ℝ) :
    (∫ z : ι → ℝ, f z • gaussianProductDensityDerivative v c z
      ∂(Measure.pi fun _ : ι => (volume : Measure ℝ))) =
      ∑ i : ι, (∫ z : ι → ℝ, (z i - c i) / v * f z
        ∂(Measure.pi fun j => gaussianReal (c j) v)) •
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) := by
  let μ := Measure.pi fun j => gaussianReal (c j) v
  let S (z : ι → ℝ) := ∑ i : ι, ((z i - c i) / v * f z) •
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)
  have hterm (i : ι) : Integrable (fun z : ι → ℝ =>
      ((z i - c i) / v * f z) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) μ :=
    (gaussianCoordinate_first_kernel_integrable_bound c v hv hf hfbound i).1.smul_const _
  calc
    _ = ∫ z : ι → ℝ, (∏ i, gaussianPDFReal (c i) v (z i)) • S z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [gaussianProductDensityDerivative_eq_density_smul_score]
      simp only [S, Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ring
    _ = ∫ z : ι → ℝ, S z ∂μ :=
      (integral_pi_gaussianReal_eq_integral_smul c v hv S).symm
    _ = _ := by
      rw [show (∫ z : ι → ℝ, S z ∂μ) =
        ∑ i : ι, ∫ z : ι → ℝ, ((z i - c i) / v * f z) •
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) ∂μ from
        integral_finset_sum Finset.univ (fun i _ => hterm i)]
      simp_rw [integral_smul_const]
      rfl

/-- The derivative of a bounded measurable product Gaussian average has
operator norm at most the number of coordinates times one plus the inverse
variance. [OD14, §11.1; §11.4, Gaussian smoothing]
The explicit constant is a convenient nonsharp bound.

**Proof sketch.** Express the derivative as the sum of coordinate-score
expectations times projections. Each expectation is bounded by one plus the
inverse variance, and each projection has operator norm at most one. Sum the
resulting norm bounds. -/
lemma norm_integral_gaussianProductDensityDerivative_smul_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) (c : ι → ℝ) :
    ‖∫ z : ι → ℝ, f z • gaussianProductDensityDerivative v c z
      ∂(Measure.pi fun _ : ι => (volume : Measure ℝ))‖ ≤
      (Fintype.card ι : ℝ) * (1 + 1 / (v : ℝ)) := by
  rw [integral_gaussianProductDensityDerivative_smul_eq_sum hf hfbound v hv c]
  calc
    _ ≤ ∑ _i : ι, (1 + 1 / (v : ℝ)) := by
      apply norm_sum_le_of_le
      intro i _
      have hproj := norm_coordinateProjection_le_one i
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) hproj).trans
        (gaussianCoordinate_first_kernel_integrable_bound c v hv hf hfbound i).2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end BooleanAnalysis.GaussianSpace
