/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.GaussianDensity
import Mathlib.MeasureTheory.Integral.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Densities and affine transformations of finite Gaussian products

## Main definitions

The existing real Gaussian laws and finite-product measures are reused.

## Main results

* A finite product of nondegenerate real Gaussian laws has the product density.
* Integration against that product law equals integration against its density.
* Coordinatewise affine maps preserve the specified Gaussian product laws.

These are the law and integration adapters for differentiating an averaged
indicator against a fixed product Lebesgue measure. No new Gaussian measure
or noise operator is introduced.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Gaussian product laws and smoothing.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- A coordinate projection from a finite real product with its supremum
norm has operator norm at most one. [OD14, §11.1, finite coordinate products]

**Proof sketch.** Each coordinate norm is bounded by the product supremum
norm. Apply the operator-norm upper-bound criterion. -/
lemma norm_coordinateProjection_le_one {ι : Type*} [Fintype ι] (i : ι) :
    ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm x i

/-- Independent real Gaussian coordinates have Lebesgue density equal to the
product of their scalar densities. [OD14, §11.1, product Gaussian law]

**Proof sketch.** Compare both measures on coordinate rectangles. The
nonnegative density integral separates into the product of scalar Gaussian
rectangle probabilities by finite-product integration. -/
lemma pi_gaussianReal_eq_withDensity {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (Measure.pi fun i => gaussianReal (c i) v) =
      (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity
        (fun z : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal (c i) v (z i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal
      ((Integrable.fintype_prod fun i => integrable_gaussianPDFReal (c i) v).restrict)
      (Eventually.of_forall fun z => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _),
    Measure.restrict_pi_pi, integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg fun z => gaussianPDFReal_nonneg _ _ _)]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply_eq_integral (c i) hv (s i)).symm

/-- Integration against a finite product of real Gaussian laws equals Lebesgue
integration against the product density. [OD14, §11.1, product Gaussian law]

**Proof sketch.** Apply the established product-density identity and the
integration formula for a measure with density. Nonnegativity identifies the
real density with the real part of its nonnegative embedding. -/
lemma integral_pi_gaussianReal_eq_integral_smul {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (f : (ι → ℝ) → E) :
    (∫ z : ι → ℝ, f z ∂(Measure.pi fun i => gaussianReal (c i) v)) =
      ∫ z : ι → ℝ, (∏ i, gaussianPDFReal (c i) v (z i)) • f z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ)) := by
  have hmeas : Measurable (fun z : ι → ℝ => ∏ i, gaussianPDFReal (c i) v (z i)) := by
    exact Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal (c i) v).comp (measurable_pi_apply i)
  rw [pi_gaussianReal_eq_withDensity c v hv,
    integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal
      (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _)]

/-- Coordinatewise affine maps send independent standard Gaussian coordinates
to independent Gaussians with the specified means and squared scale variance.
[OD14, §11.1, affine Gaussian transformations]

**Proof sketch.** The scalar scaling and translation laws identify each
coordinate's pushforward. A product of coordinatewise measure-preserving maps
preserves the corresponding product laws. The scale may be zero or negative. -/
lemma measurePreserving_gaussianAffine_pi {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (s : ℝ) :
    MeasurePreserving (fun y : ι → ℝ => fun i => c i + s * y i)
      (Measure.pi fun _ : ι => standardGaussianMeasure)
      (Measure.pi fun i => gaussianReal (c i) ⟨s ^ 2, sq_nonneg s⟩) := by
  refine measurePreserving_pi (fun _ : ι => standardGaussianMeasure)
    (fun i => gaussianReal (c i) ⟨s ^ 2, sq_nonneg s⟩)
    (f := fun i y => c i + s * y) fun i => ⟨by fun_prop, ?_⟩
  dsimp only
  rw [show (fun y : ℝ => c i + s * y) =
      (fun z : ℝ => c i + z) ∘ (fun y : ℝ => s * y) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), standardGaussianMeasure,
    gaussianReal_map_const_mul, gaussianReal_map_const_add]
  simp

/-- Averaging a measurable real function over an affine image of independent
standard Gaussian coordinates equals integrating it against the corresponding
product density. The common scale may have either nonzero sign.
[OD14, §11.1, Gaussian smoothing]

**Proof sketch.** Push the product standard Gaussian law through its affine
coordinate maps. The resulting independent Gaussian coordinates have the
specified means and squared scale variance. Apply the product-density
integration formula. -/
lemma integral_affine_gaussian_pi_eq_density {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (s : ℝ) (hs : s ≠ 0) {f : (ι → ℝ) → ℝ} (hf : Measurable f) :
    (∫ y : ι → ℝ, f (fun i => c i + s * y i)
      ∂(Measure.pi fun _ : ι => standardGaussianMeasure)) =
      ∫ z : ι → ℝ, (∏ i, gaussianPDFReal (c i) ⟨s ^ 2, sq_nonneg s⟩ (z i)) * f z
        ∂(Measure.pi fun _ : ι => (volume : Measure ℝ)) := by
  let v : ℝ≥0 := ⟨s ^ 2, sq_nonneg s⟩
  have hv : v ≠ 0 := by
    intro h
    have hsq : s ^ 2 = 0 := congrArg Subtype.val h
    exact hs (eq_zero_of_pow_eq_zero hsq)
  have hp := measurePreserving_gaussianAffine_pi c s
  calc
    _ = ∫ z : ι → ℝ, f z ∂(Measure.pi fun i => gaussianReal (c i) v) := by
      have h := integral_map_of_stronglyMeasurable
        (μ := Measure.pi fun _ : ι => standardGaussianMeasure) hp.measurable hf.stronglyMeasurable
      rw [hp.map_eq] at h
      exact h.symm
    _ = _ := by
      simpa only [smul_eq_mul] using
        integral_pi_gaussianReal_eq_integral_smul c v hv f

/-- The centered coordinate square is genuinely integrable under a finite
product of real Gaussian laws. [OD14, §11.1, Gaussian product moments]

**Proof sketch.** The scalar Gaussian has finite second moment; subtracting
its mean preserves this property. Transfer its integrable square through the
measure-preserving coordinate evaluation. -/
lemma integrable_centered_sq_gaussianCoordinate {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ℝ≥0) (i : ι) :
    Integrable (fun z : ι → ℝ => (z i - c i) ^ 2)
      (Measure.pi fun j => gaussianReal (c j) v) := by
  exact (measurePreserving_eval (fun j => gaussianReal (c j) v) i).integrable_comp_of_integrable
    (((memLp_id_gaussianReal (μ := c i) (v := v) 2).sub (memLp_const (c i))).integrable_sq)

/-- Every coordinate of a product Gaussian has centered second moment equal
to the common variance parameter. [OD14, §11.1, Gaussian product moments]

**Proof sketch.** Coordinate evaluation preserves the corresponding Gaussian
marginal. Transfer the centered-square integral through that evaluation and
apply the scalar Gaussian centered-second-moment identity. -/
lemma integral_centered_sq_gaussianCoordinate {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ℝ≥0) (i : ι) :
    (∫ z : ι → ℝ, (z i - c i) ^ 2 ∂(Measure.pi fun j => gaussianReal (c j) v)) = v := by
  have hp := measurePreserving_eval (fun j => gaussianReal (c j) v) i
  have h := integral_map_of_stronglyMeasurable
    (μ := Measure.pi fun j => gaussianReal (c j) v) hp.measurable
    (show StronglyMeasurable (fun z : ℝ => (z - c i) ^ 2) from by fun_prop)
  rw [hp.map_eq] at h
  exact h.symm.trans (integral_centered_sq_gaussianReal (c i) v)

end BooleanAnalysis.GaussianSpace
