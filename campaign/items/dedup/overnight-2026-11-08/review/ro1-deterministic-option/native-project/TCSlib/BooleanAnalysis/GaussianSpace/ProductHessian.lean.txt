/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.ProductDifferentiation
import TCSlib.BooleanAnalysis.GaussianSpace.ProductBounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Second derivatives of product Gaussian densities

## Main definitions

* `gaussianProductDensityScore`: the centered coordinate score, as a linear map.
* `gaussianProductDensityHessian`: the ordinary second derivative in the mean,
  as a curried continuous bilinear map.

## Main results

* Differentiating the first product-density derivative gives this Hessian.
* Each coordinate pair has the usual centered quadratic kernel, with an
  inverse-variance correction on the diagonal.
* Local integrable envelopes justify differentiating the integrated first derivative.
  Gaussian moment bounds then give its global Lipschitz constant.

These formulas support the Lipschitz derivative bound for Gaussian averages.
The existing scalar densities, finite-product law and ordinary derivative are
used throughout.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian smoothing, and §11.4,
  the smooth indicator approximation for Gaussian isoperimetry.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- The logarithmic derivative of a product Gaussian density in its mean vector. [OD14, §11.1; §11.4, Gaussian smoothing] -/
noncomputable def gaussianProductDensityScore {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (c z : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, ((z i - c i) / v) • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)

/-- The mean derivative of the product Gaussian score is the negative inverse
variance times the coordinate inner-product map. [OD14, §11.1; §11.4, Gaussian smoothing] -/
lemma hasFDerivAt_gaussianProductDensityScore {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (c z : ι → ℝ) :
    HasFDerivAt (fun m : ι → ℝ => gaussianProductDensityScore v m z)
      (∑ i, (-1 / (v : ℝ)) •
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) c := by
  have h (i : ι) : HasFDerivAt (fun m : ι → ℝ => ((z i - m i) / v) •
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))
      ((-1 / (v : ℝ)) •
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) c := by
    convert (((hasFDerivAt_const (z i) c).sub
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt).mul_const (v : ℝ)⁻¹).smul_const
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) using 1
    ext x y
    simp
    ring
  exact HasFDerivAt.fun_sum fun i _ => h i

/-- The second mean derivative of the product Gaussian density, as a curried
continuous bilinear map. [OD14, §11.1; §11.4, Gaussian smoothing] -/
noncomputable def gaussianProductDensityHessian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ℝ≥0) (c z : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  (∏ i, gaussianPDFReal (c i) v (z i)) •
      (∑ i, (-1 / (v : ℝ)) •
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) +
    (gaussianProductDensityDerivative v c z).smulRight (gaussianProductDensityScore v c z)

/-- The product Gaussian density derivative is itself Fréchet differentiable
in the mean vector, with the Gaussian density Hessian as its derivative. [OD14, §11.1; §11.4, Gaussian smoothing] -/
lemma hasFDerivAt_gaussianProductDensityDerivative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ℝ≥0) (c z : ι → ℝ) :
    HasFDerivAt (fun m : ι → ℝ => gaussianProductDensityDerivative v m z)
      (gaussianProductDensityHessian v c z) c := by
  have h := (hasFDerivAt_gaussianProductDensity v c z).smul
    (hasFDerivAt_gaussianProductDensityScore v c z)
  simpa only [gaussianProductDensityHessian, gaussianProductDensityScore,
    gaussianProductDensityDerivative_eq_density_smul_score] using h

/-- Every pair of coordinates in the Gaussian density Hessian has the usual
centered quadratic kernel, with an inverse-variance correction on the diagonal.
[OD14, §11.1; §11.4, Gaussian smoothing]

**Proof sketch.** Evaluate the bilinear maps on two vectors and expand the
product of the two score sums. The derivative of the score supplies the diagonal
correction; distributivity and scalar algebra give the displayed double sum. -/
lemma gaussianProductDensityHessian_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ℝ≥0) (c z : ι → ℝ) :
    gaussianProductDensityHessian v c z =
      ∑ i, ∑ j, ((((z i - c i) * (z j - c j) / (v : ℝ) ^ 2 -
        if i = j then 1 / (v : ℝ) else 0) * ∏ k, gaussianPDFReal (c k) v (z k))) •
        (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).smulRight
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) := by
  ext h k
  simp only [gaussianProductDensityHessian, gaussianProductDensityScore,
    gaussianProductDensityDerivative_eq_density_smul_score,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp_rw [sub_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, Finset.sum_mul]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- A common scalar bound on the densities and second derivative kernels
also bounds any squared coordinate score times the full product density. [OD14, §11.1; §11.4, Gaussian smoothing]

**Proof sketch.** Add the density divided by the variance to its diagonal
second-derivative kernel to obtain the squared-score density. Apply the common
scalar bounds, then multiply by the remaining coordinate densities and combine
their product bounds. -/
lemma gaussianProductDensity_squaredScore_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ℝ≥0) (c z a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hpdf : ∀ i, gaussianPDFReal (c i) v (z i) ≤ a i)
    (hsecond : ∀ i,
      |((z i - c i) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * gaussianPDFReal (c i) v (z i)| ≤ a i)
    (i : ι) :
    ((z i - c i) ^ 2 / (v : ℝ) ^ 2) * (∏ j, gaussianPDFReal (c j) v (z j)) ≤
      (1 + 1 / (v : ℝ)) * ∏ j, a j := by
  have hscalar : ((z i - c i) ^ 2 / (v : ℝ) ^ 2) * gaussianPDFReal (c i) v (z i) ≤
      (1 + 1 / (v : ℝ)) * a i := by
    calc
      _ = ((z i - c i) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * gaussianPDFReal (c i) v (z i) +
          (1 / (v : ℝ)) * gaussianPDFReal (c i) v (z i) := by ring
      _ ≤ |((z i - c i) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * gaussianPDFReal (c i) v (z i)| +
          (1 / (v : ℝ)) * gaussianPDFReal (c i) v (z i) :=
        add_le_add_right (le_abs_self _) _
      _ ≤ a i + (1 / (v : ℝ)) * a i :=
        add_le_add (hsecond i) (mul_le_mul_of_nonneg_left (hpdf i) (by positivity))
      _ = _ := by ring
  calc
    _ = (∏ j ∈ Finset.univ.erase i, gaussianPDFReal (c j) v (z j)) *
        (((z i - c i) ^ 2 / (v : ℝ) ^ 2) * gaussianPDFReal (c i) v (z i)) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      ring
    _ ≤ (∏ j ∈ Finset.univ.erase i, a j) * ((1 + 1 / (v : ℝ)) * a i) := by
      apply mul_le_mul
      · exact Finset.prod_le_prod (fun j _ => gaussianPDFReal_nonneg _ _ _)
          (fun j _ => hpdf j)
      · exact hscalar
      · exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
          (gaussianPDFReal_nonneg _ _ _)
      · exact Finset.prod_nonneg fun j _ => ha j
    _ = _ := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      ring

/-- Common scalar envelopes control every Hessian coordinate kernel times
the full product density, uniformly over bounded means. [OD14, §11.1; §11.4, Gaussian smoothing]

**Proof sketch.** Use the quadratic Hessian-score majorant, multiplied by
the nonnegative product density. The squared-coordinate terms are bounded by
the squared-score estimates and the constant term by the density bound. -/
lemma abs_gaussianProductDensity_hessianCoefficient_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : ℝ≥0) (hv : v ≠ 0) (c z a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hpdf : ∀ i, gaussianPDFReal (c i) v (z i) ≤ a i)
    (hsecond : ∀ i,
      |((z i - c i) ^ 2 / (v : ℝ) ^ 2 - 1 / v) * gaussianPDFReal (c i) v (z i)| ≤ a i)
    (i j : ι) :
    |(((z i - c i) * (z j - c j) / (v : ℝ) ^ 2 -
        if i = j then 1 / (v : ℝ) else 0) * ∏ k, gaussianPDFReal (c k) v (z k))| ≤
      (1 + 2 / (v : ℝ)) * ∏ k, a k := by
  have hK : (∏ k, gaussianPDFReal (c k) v (z k)) ≤ ∏ k, a k :=
    Finset.prod_le_prod (fun k _ => gaussianPDFReal_nonneg _ _ _) (fun k _ => hpdf k)
  have hKpos : 0 ≤ ∏ k, gaussianPDFReal (c k) v (z k) :=
    Finset.prod_nonneg fun k _ => gaussianPDFReal_nonneg _ _ _
  have hi := gaussianProductDensity_squaredScore_le v c z a ha hpdf hsecond i
  have hj := gaussianProductDensity_squaredScore_le v c z a ha hpdf hsecond j
  have hq := abs_productHessian_mul_le c z v hv i j 1 (by norm_num)
  rw [mul_one] at hq
  rw [abs_mul, abs_of_nonneg hKpos]
  calc
    _ ≤ (((z i - c i) ^ 2 + (z j - c j) ^ 2) / (2 * (v : ℝ) ^ 2) + 1 / v) *
        ∏ k, gaussianPDFReal (c k) v (z k) := mul_le_mul_of_nonneg_right hq hKpos
    _ = ((((z i - c i) ^ 2 / (v : ℝ) ^ 2) * ∏ k, gaussianPDFReal (c k) v (z k)) +
        (((z j - c j) ^ 2 / (v : ℝ) ^ 2) * ∏ k, gaussianPDFReal (c k) v (z k))) / 2 +
        (1 / (v : ℝ)) * ∏ k, gaussianPDFReal (c k) v (z k) := by ring
    _ ≤ (((1 + 1 / (v : ℝ)) * ∏ k, a k) +
        ((1 + 1 / (v : ℝ)) * ∏ k, a k)) / 2 + (1 / (v : ℝ)) * ∏ k, a k :=
      add_le_add (div_le_div_of_nonneg_right (add_le_add hi hj) (by norm_num))
        (mul_le_mul_of_nonneg_left hK (by positivity))
    _ = _ := by ring

/-- The Gaussian density Hessian is jointly continuous in the mean and
integration vectors. [OD14, §11.1; §11.4, Gaussian smoothing]

**Proof sketch.** The coordinate Gaussian densities and centered scores
are continuous jointly in means and inputs. Finite sums, products, and
continuous linear-map constructions preserve continuity. -/
lemma continuous_gaussianProductDensityHessian_joint {ι : Type*} [Fintype ι]
    [DecidableEq ι] (v : ℝ≥0) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => gaussianProductDensityHessian v p.1 p.2) := by
  letI : NormedAddCommGroup ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) := inferInstance
  simp_rw [gaussianProductDensityHessian_eq_sum]
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro j _
  apply Continuous.smul
  · unfold gaussianPDFReal
    fun_prop
  · exact continuous_const

/-- The operator norm of a coordinate tensor matrix is at most the sum
of the absolute values of its coefficients. [OD14, §11.1; §11.4, Gaussian smoothing]

**Proof sketch.** Each coordinate projection has norm at most one, so
each tensor of two projections has norm at most one. Apply the triangle
inequality twice and bound every scalar multiple by its absolute coefficient. -/
lemma norm_sum_sum_coordinateTensor_le {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) :
    ‖∑ i, ∑ j, a i j •
      (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ ∑ i, ∑ j, |a i j| := by
  letI : NormedAddCommGroup ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) := inferInstance
  apply norm_sum_le_of_le
  intro i _
  apply norm_sum_le_of_le
  intro j _
  rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
  apply mul_le_of_le_one_right (abs_nonneg _)
  calc
    _ ≤ 1 * 1 := mul_le_mul (norm_coordinateProjection_le_one j)
      (norm_coordinateProjection_le_one i) (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

/-- The Hessian of the product Gaussian density admits an integrable envelope
uniformly on bounded mean vectors.
[OD14, §11.1; §11.4, Gaussian smoothing]

**Proof sketch.** Each coordinate Hessian kernel is bounded by a fixed multiple
of the product of the common scalar envelopes. The operator norm is at most the
sum of the absolute coordinate coefficients. -/
lemma gaussianProductDensityHessian_dominated {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ℝ≥0) (hv : v ≠ 0) (M : ℝ) (hM : 0 ≤ M) :
    ∃ b : (ι → ℝ) → ℝ,
      Integrable b (Measure.pi fun _ : ι => (volume : Measure ℝ)) ∧
      (∀ z, 0 ≤ b z) ∧ ∀ m : ι → ℝ, (∀ i, |m i| ≤ M) → ∀ z : ι → ℝ,
      ‖gaussianProductDensityHessian v m z‖ ≤ b z := by
  obtain ⟨a, ha, hapos, habound⟩ := gaussianPDFReal_two_derivatives_dominated v hv M hM
  have haint : Integrable (fun z : ι → ℝ => ∏ i, a (z i))
      (Measure.pi fun _ : ι => (volume : Measure ℝ)) := Integrable.fintype_prod fun _ => ha
  refine ⟨fun z => (Fintype.card ι : ℝ) ^ 2 * (1 + 2 / (v : ℝ)) * ∏ i, a (z i),
    haint.const_mul _, fun z => mul_nonneg (by positivity)
      (Finset.prod_nonneg fun i _ => hapos (z i)), ?_⟩
  intro m hm z
  rw [gaussianProductDensityHessian_eq_sum]
  calc
    _ ≤ ∑ i, ∑ j, |(((z i - m i) * (z j - m j) / (v : ℝ) ^ 2 -
        if i = j then 1 / (v : ℝ) else 0) * ∏ k, gaussianPDFReal (m k) v (z k))| :=
      norm_sum_sum_coordinateTensor_le _
    _ ≤ ∑ _i : ι, ∑ _j : ι, (1 + 2 / (v : ℝ)) * ∏ k, a (z k) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact abs_gaussianProductDensity_hessianCoefficient_le v hv m z (fun k => a (z k))
        (fun k => hapos (z k)) (fun k => (habound (m k) (hm k) (z k)).1)
        (fun k => (habound (m k) (hm k) (z k)).2.2) i j
    _ = _ := by simp; ring

-- Reuse the canonical structures while elaborating nested-map integrability.
noncomputable local instance {ι : Type*} [Fintype ι] :
    NormedAddCommGroup ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) := inferInstance

noncomputable local instance {ι : Type*} [Fintype ι] :
    NormedSpace ℝ ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) := inferInstance

/-- A bounded measurable multiplier preserves genuine integrability of the
Gaussian product-density Hessian. [OD14, §11.1; §11.4, Gaussian smoothing]

**Proof sketch.** The jointly continuous Hessian and measurable multiplier
make the integrand measurable. Its norm is dominated by the local integrable
Hessian envelope at the specified mean vector. -/
lemma integrable_gaussianProductDensityHessian_smul {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) (c : ι → ℝ) :
    Integrable (fun z : ι → ℝ => f z • gaussianProductDensityHessian v c z)
      (Measure.pi fun _ : ι => (volume : Measure ℝ)) := by
  letI : NormedAddCommGroup ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) := inferInstance
  obtain ⟨b, hb, _, hbound⟩ := gaussianProductDensityHessian_dominated (ι := ι) v hv
    ‖c‖ (norm_nonneg c)
  have hmeas : Measurable (fun z : ι → ℝ => gaussianProductDensityHessian v c z) :=
    ((continuous_gaussianProductDensityHessian_joint v).comp
      (continuous_const.prodMk continuous_id)).measurable
  refine hb.mono' (hf.smul hmeas).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hfbound z)).trans
    (hbound c (fun i => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c i) z)

/-- The derivative of a bounded measurable function's product Gaussian
average is itself Fréchet differentiable, with derivative given by the integrated
Gaussian Hessian. [OD14, §11.1; §11.4, Gaussian smoothing]

**Proof sketch.** Use genuine integrability of the first derivative, and apply
parametric differentiation with the local integrable Hessian envelope. -/
lemma hasFDerivAt_integral_gaussianProductDensityDerivative {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) (c : ι → ℝ) :
    HasFDerivAt (fun m : ι → ℝ =>
      ∫ z : ι → ℝ, f z • gaussianProductDensityDerivative v m z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ)))
      (∫ z : ι → ℝ, f z • gaussianProductDensityHessian v c z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ))) c := by
  obtain ⟨b, hb, _, hbound⟩ := gaussianProductDensityHessian_dominated (ι := ι) v hv
    (‖c‖ + 1) (by positivity)
  have hmeas : Measurable (fun z : ι → ℝ => gaussianProductDensityHessian v c z) :=
    ((continuous_gaussianProductDensityHessian_joint v).comp
      (continuous_const.prodMk continuous_id)).measurable
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun m z : ι → ℝ => f z • gaussianProductDensityDerivative v m z)
    (F' := fun m z : ι → ℝ => f z • gaussianProductDensityHessian v m z)
    (bound := b) (show (0 : ℝ) < 1 by norm_num)
    (Eventually.of_forall fun m =>
      (hf.smul (continuous_gaussianProductDensityDerivative v m).measurable).aestronglyMeasurable)
    (integrable_gaussianProductDensityDerivative_smul hf hfbound v hv c)
    (hf.smul hmeas).aestronglyMeasurable ?_ hb ?_
  · filter_upwards [] with z m hm
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hfbound z)).trans
      (hbound m (abs_coordinate_le_of_mem_ball hm) z)
  · exact Eventually.of_forall fun z m _ =>
      (hasFDerivAt_gaussianProductDensityDerivative v m z).const_smul (f z)

/-- The integrated Gaussian Hessian equals the double sum of coordinate
Hessian-score expectations times the corresponding coordinate tensors.
[OD14, §11.1; §11.4, Gaussian smoothing]

**Proof sketch.** Expand the Hessian into coordinate kernels and transfer the
product density to the Gaussian product law. Every bounded measurable
coordinate kernel is genuinely integrable, so its scalar multiple of a fixed
coordinate tensor and the finite double sum commute with integration. -/
lemma integral_gaussianProductDensityHessian_smul_eq_sum {ι : Type*}
    [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) (c : ι → ℝ) :
    (∫ z : ι → ℝ, f z • gaussianProductDensityHessian v c z
      ∂(Measure.pi fun _ : ι => (volume : Measure ℝ))) =
      ∑ i : ι, ∑ j : ι, (∫ z : ι → ℝ,
        (((z i - c i) * (z j - c j) / (v : ℝ) ^ 2 -
          if i = j then 1 / (v : ℝ) else 0) * f z)
        ∂(Measure.pi fun k => gaussianReal (c k) v)) •
          (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).smulRight
            (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) := by
  letI : NormedAddCommGroup ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) := inferInstance
  let μ := Measure.pi fun k => gaussianReal (c k) v
  let T (i j : ι) := (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)
  let K (i j : ι) (z : ι → ℝ) :=
    ((z i - c i) * (z j - c j) / (v : ℝ) ^ 2 -
      if i = j then 1 / (v : ℝ) else 0) * f z
  let S (z : ι → ℝ) := ∑ i : ι, ∑ j : ι, K i j z • T i j
  have hterm (i j : ι) : Integrable (fun z : ι → ℝ => K i j z • T i j) μ :=
    (integrable_productHessian_mul c v hv hf hfbound i j).smul_const _
  have hinner (i : ι) : Integrable (fun z : ι → ℝ => ∑ j : ι, K i j z • T i j) μ :=
    integrable_finset_sum Finset.univ (fun j _ => hterm i j)
  calc
    _ = ∫ z : ι → ℝ, (∏ i, gaussianPDFReal (c i) v (z i)) • S z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [gaussianProductDensityHessian_eq_sum]
      simp only [S, Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [K, T]
      congr 1
      ring
    _ = ∫ z : ι → ℝ, S z ∂μ :=
      (integral_pi_gaussianReal_eq_integral_smul c v hv S).symm
    _ = _ := by
      rw [show (∫ z : ι → ℝ, S z ∂μ) =
        ∑ i : ι, ∫ z : ι → ℝ, (∑ j : ι, K i j z • T i j) ∂μ from
        integral_finset_sum Finset.univ (fun i _ => hinner i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum Finset.univ (fun j _ => hterm i j)]
      simp_rw [integral_smul_const]
      rfl

/-- The second derivative of a bounded measurable Gaussian average has
operator norm at most twice the square of the number of coordinates divided
by the variance. [OD14, §11.1; §11.4, Gaussian smoothing]
The stated dimension factor is a convenient nonsharp bound.

**Proof sketch.** The integrated coordinate-kernel formula has a tensor of
norm at most one for each coordinate pair. Each scalar expectation is at most
twice the inverse variance in absolute value. Sum over the coordinate pairs. -/
lemma norm_integral_gaussianProductDensityHessian_smul_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) (c : ι → ℝ) :
    ‖∫ z : ι → ℝ, f z • gaussianProductDensityHessian v c z
      ∂(Measure.pi fun _ : ι => (volume : Measure ℝ))‖ ≤
      (Fintype.card ι : ℝ) ^ 2 * (2 / (v : ℝ)) := by
  rw [integral_gaussianProductDensityHessian_smul_eq_sum hf hfbound v hv c]
  refine (norm_sum_sum_coordinateTensor_le _).trans ?_
  calc
    _ ≤ ∑ _i : ι, ∑ _j : ι, 2 / (v : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact abs_integral_productHessian_mul_le c v hv hfbound i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The derivative of the product Gaussian average of a measurable function
bounded by one is globally Lipschitz in the mean vector.
[OD14, §11.1; §11.4, Gaussian smoothing]

**Proof sketch.** Its derivative is the integrated Gaussian Hessian, whose
operator norm is uniformly bounded by twice the square of the dimension divided
by the variance. Apply the mean value inequality. -/
lemma lipschitzWith_integral_gaussianProductDensityDerivative {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hfbound : ∀ z, |f z| ≤ 1)
    (v : ℝ≥0) (hv : v ≠ 0) :
    LipschitzWith ((Fintype.card ι : ℝ≥0) ^ 2 * (2 / v))
      (fun c : ι → ℝ => ∫ z : ι → ℝ, f z • gaussianProductDensityDerivative v c z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ))) := by
  refine lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    (fun c => (hasFDerivAt_integral_gaussianProductDensityDerivative hf hfbound v hv c).differentiableAt)
    (fun c => ?_)
  change ‖fderiv ℝ (fun m : ι → ℝ =>
      ∫ z : ι → ℝ, f z • gaussianProductDensityDerivative v m z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ))) c‖ ≤
      (Fintype.card ι : ℝ) ^ 2 * (2 / (v : ℝ))
  rw [(hasFDerivAt_integral_gaussianProductDensityDerivative hf hfbound v hv c).fderiv]
  exact norm_integral_gaussianProductDensityHessian_smul_le hf hfbound v hv c

end BooleanAnalysis.GaussianSpace
