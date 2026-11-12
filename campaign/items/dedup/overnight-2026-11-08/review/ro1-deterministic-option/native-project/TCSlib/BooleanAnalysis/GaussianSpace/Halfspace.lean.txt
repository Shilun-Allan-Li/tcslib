/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TCSlib.BooleanAnalysis.GaussianSpace.Rotation
import TCSlib.LearningTheory.JohnsonLindenstrauss.RowDistribution

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian rotation sensitivity of halfspaces

## Main definitions

No new Gaussian law or surface-area definition is introduced.

## Main results

* measurePreserving_gaussianProjection: unit Gaussian projection law.
* integral_abs_gaussianProjection: absolute moments of arbitrary Gaussian linear forms.
* rotationSensitivity_halfspace_eq_scalar: reduction to a scalar crossing event.
* halfspace_rotation_quotient_tendsto: the normalized crossing limit.

The analytic argument conditions on the second Gaussian coordinate, differentiates
the resulting Gaussian CDF increment, and uses dominated convergence. The projection
law reuses the existing weighted-sum result from the Johnson–Lindenstrauss development.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1 and §11.4, Proposition 11.49.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- A unit linear functional sends the product standard Gaussian law to the
one-dimensional standard Gaussian law. [OD14, §11.1, Notation 11.1]

**Proof sketch.** Specialize the existing weighted-sum Gaussian distribution law
to the independent coordinate evaluations. The squared coefficients sum to one,
so the projected Gaussian has mean zero and variance one. -/
lemma measurePreserving_gaussianProjection {n : ℕ} (a : Fin n → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) :
    MeasurePreserving (fun z : Fin n → ℝ => ∑ i, a i * z i)
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) standardGaussianMeasure := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  refine ⟨by fun_prop, ?_⟩
  have h := sum_scaled_iid_gaussian_map
    (μ := Measure.pi fun _ : Fin n => standardGaussianMeasure)
    (Y := fun (i : Fin n) (z : Fin n → ℝ) => z i) (σ₀ := 1)
    (fun i => measurable_pi_apply i)
    (fun i => by simpa only [standardGaussianMeasure] using
      (measurePreserving_eval (fun _ : Fin n => standardGaussianMeasure) i).map_eq)
    (ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin n => standardGaussianMeasure)
      (X := fun _ : Fin n => (id : ℝ → ℝ))
      (fun _ => measurable_id.aemeasurable)) a Finset.univ
  simpa [standardGaussianMeasure, ha] using h

/-- The conditional Gaussian threshold probability has derivative minus the
Gaussian density times the second coordinate at angle zero. -/
private lemma hasDerivAt_rotated_gaussianCDF (t y : ℝ) :
    HasDerivAt
      (fun θ : ℝ => standardGaussianCDF ((t - Real.sin θ * y) / Real.cos θ) -
        standardGaussianCDF t)
      (-standardGaussianPDF t * y) 0 := by
  have hb : HasDerivAt (fun θ : ℝ => (t - Real.sin θ * y) / Real.cos θ) (-y) 0 := by
    convert ((hasDerivAt_const (0 : ℝ) t).sub
      ((Real.hasDerivAt_sin 0).mul_const y)).div (Real.hasDerivAt_cos 0)
      (by norm_num) using 1
    norm_num
  have h := (hasDerivAt_standardGaussianCDF
    ((t - Real.sin 0 * y) / Real.cos 0)).comp 0 hb
  simpa [mul_neg] using h.sub_const (standardGaussianCDF t)

/-- The absolute conditional crossing quotient tends to the density times the
absolute second coordinate as the angle decreases to zero. -/
private lemma rotated_gaussianCDF_quotient_tendsto (t y : ℝ) :
    Tendsto (fun θ : ℝ =>
      |standardGaussianCDF ((t - Real.sin θ * y) / Real.cos θ) - standardGaussianCDF t| / θ)
      (𝓝[>] (0 : ℝ)) (𝓝 (standardGaussianPDF t * |y|)) := by
  have h := (hasDerivAt_rotated_gaussianCDF t y).tendsto_slope_zero_right.abs
  simp only [zero_add, Real.sin_zero, zero_mul, sub_zero, Real.cos_zero, div_one,
    sub_self, sub_zero, smul_eq_mul, abs_mul, abs_neg,
    abs_of_pos (standardGaussianPDF_pos t)] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  change 0 < θ at hθ
  simp [abs_of_pos hθ, div_eq_mul_inv, mul_comm]

/-- The standard Gaussian density attains its maximum at zero. -/
private lemma standardGaussianPDF_le_at_zero (x : ℝ) :
    standardGaussianPDF x ≤ standardGaussianPDF 0 := by
  simp only [standardGaussianPDF_eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, neg_zero, zero_div, Real.exp_zero, mul_one]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.exp_le_one_iff.mpr (show -x ^ 2 / 2 ≤ 0 by nlinarith [sq_nonneg x]))
    (show 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ by positivity)

/-- A Gaussian CDF increment is bounded by the density at zero times the
distance between its endpoints. -/
private lemma abs_standardGaussianCDF_sub_le (x y : ℝ) :
    |standardGaussianCDF x - standardGaussianCDF y| ≤
      standardGaussianPDF 0 * |x - y| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (Set.univ : Set ℝ)) =>
        (hasDerivAt_standardGaussianCDF z).hasDerivWithinAt)
      (fun z _ => (abs_of_pos (standardGaussianPDF_pos z)).trans_le
        (standardGaussianPDF_le_at_zero z)) convex_univ (Set.mem_univ y) (Set.mem_univ x)

/-- For angles between zero and one, the conditional crossing quotient is
bounded by an integrable linear function of the absolute coordinates.

**Proof sketch.** The cosine is at least one half, and the sine and the cosine
increment are bounded by the angle. These bounds control the displacement of
the conditional threshold. Apply the global bound on Gaussian CDF increments. -/
private lemma rotated_gaussianCDF_quotient_le (t y θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    |standardGaussianCDF ((t - Real.sin θ * y) / Real.cos θ) - standardGaussianCDF t| / θ ≤
      2 * standardGaussianPDF 0 * (|t| + |y|) := by
  have hcos : 1 / 2 ≤ Real.cos θ := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := θ), sq_nonneg (1 - θ)]
  have hcospos : 0 < Real.cos θ := by linarith
  have hcos1 : |1 - Real.cos θ| ≤ θ := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one θ))]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
  have hsin : |Real.sin θ| ≤ θ :=
    Real.abs_sin_le_abs.trans_eq (abs_of_pos hθ)
  have hb : |(t - Real.sin θ * y) / Real.cos θ - t| ≤
      2 * θ * (|t| + |y|) := by
    rw [div_sub' hcospos.ne', abs_div, abs_of_pos hcospos]
    apply (div_le_iff₀ hcospos).mpr
    calc
      |t - Real.sin θ * y - Real.cos θ * t| =
          |t * (1 - Real.cos θ) - Real.sin θ * y| := by congr 1; ring
      _ ≤ |t| * |1 - Real.cos θ| + |Real.sin θ| * |y| := by
        simpa only [sub_zero, zero_sub, abs_neg, abs_mul] using
          abs_sub_le (t * (1 - Real.cos θ)) 0 (Real.sin θ * y)
      _ ≤ |t| * θ + θ * |y| := by gcongr
      _ = θ * (|t| + |y|) := by ring
      _ ≤ (2 * Real.cos θ) * (θ * (|t| + |y|)) :=
        le_mul_of_one_le_left (by positivity) (by linarith)
      _ = 2 * θ * (|t| + |y|) * Real.cos θ := by ring
  apply (div_le_iff₀ hθ).mpr
  exact (abs_standardGaussianCDF_sub_le _ _).trans
    ((mul_le_mul_of_nonneg_left hb (standardGaussianPDF_pos 0).le).trans_eq (by ring))

/-- Integrated conditional crossing quotients converge to the Gaussian density
times the first absolute Gaussian moment.

**Proof sketch.** Apply dominated convergence to the pointwise derivative limit.
The preceding uniform estimate is integrable because a Gaussian has a finite
first absolute moment. -/
private lemma integral_rotated_gaussianCDF_quotient_tendsto (t : ℝ) :
    Tendsto (fun θ : ℝ => ∫ y,
      |standardGaussianCDF ((t - Real.sin θ * y) / Real.cos θ) - standardGaussianCDF t| / θ
        ∂standardGaussianMeasure)
      (𝓝[>] (0 : ℝ))
      (𝓝 (standardGaussianPDF t * ∫ y : ℝ, |y| ∂standardGaussianMeasure)) := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  have hCDF := continuous_standardGaussianCDF
  have hid : Integrable (fun y : ℝ => y) standardGaussianMeasure := by
    simpa only [standardGaussianMeasure] using
      (ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := standardGaussianMeasure) (fun y : ℝ => 2 * standardGaussianPDF 0 * (|t| + |y|))
    (Eventually.of_forall (fun θ : ℝ =>
      (show Continuous (fun y : ℝ =>
        |standardGaussianCDF ((t - Real.sin θ * y) / Real.cos θ) - standardGaussianCDF t| / θ)
        from by fun_prop).aestronglyMeasurable))
    (show ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ᵐ y ∂standardGaussianMeasure,
        ‖|standardGaussianCDF ((t - Real.sin θ * y) / Real.cos θ) - standardGaussianCDF t| / θ‖ ≤
          2 * standardGaussianPDF 0 * (|t| + |y|) from by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
      exact Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (abs_nonneg _) hθ.1.le)]
        exact rotated_gaussianCDF_quotient_le t y θ hθ.1 hθ.2)
    (((integrable_const |t|).add hid.abs).const_mul (2 * standardGaussianPDF 0))
    (Eventually.of_forall (rotated_gaussianCDF_quotient_tendsto t))
  simpa only [integral_const_mul] using hlim

/-- The Gaussian measure of the symmetric difference of two closed lower
halflines is the absolute difference of their CDF values. -/
private lemma standardGaussianMeasure_symmDiff_Iic (a b : ℝ) :
    standardGaussianMeasure.real (symmDiff (Set.Iic a) (Set.Iic b)) =
      |standardGaussianCDF b - standardGaussianCDF a| := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  simp only [standardGaussianCDF, ProbabilityTheory.cdf_eq_real]
  rcases le_total a b with hab | hba
  · rw [symmDiff_of_le (Set.Iic_subset_Iic.mpr hab),
      measureReal_diff (Set.Iic_subset_Iic.mpr hab) measurableSet_Iic,
      abs_of_nonneg (sub_nonneg.mpr (measureReal_mono (Set.Iic_subset_Iic.mpr hab)))]
  · rw [symmDiff_of_ge (Set.Iic_subset_Iic.mpr hba),
      measureReal_diff (Set.Iic_subset_Iic.mpr hba) measurableSet_Iic,
      abs_of_nonpos (sub_nonpos.mpr (measureReal_mono (Set.Iic_subset_Iic.mpr hba)))]
    ring

/-- The first absolute standard Gaussian moment is twice its density at zero.

**Proof sketch.** Write the absolute value as the identity minus twice its
restriction to the negative halfline. The Gaussian mean vanishes, and the
existing truncated first-moment formula evaluates the second integral. -/
lemma integral_abs_standardGaussian :
    (∫ y : ℝ, |y| ∂standardGaussianMeasure) = 2 * standardGaussianPDF 0 := by
  have hmean : (∫ y : ℝ, y * standardGaussianPDF y) = 0 := by
    have h := ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := 1)
    rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (by norm_num)] at h
    simpa only [standardGaussianPDF, smul_eq_mul, mul_comm] using h
  rw [standardGaussianMeasure,
    ProbabilityTheory.integral_gaussianReal_eq_integral_smul (by norm_num)]
  change (∫ y : ℝ, standardGaussianPDF y * |y|) = _
  calc
    _ = ∫ y : ℝ, y * standardGaussianPDF y -
        2 * (Set.Iic (0 : ℝ)).indicator (fun x => x * standardGaussianPDF x) y := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ Set.Iic (0 : ℝ)
      · rw [Set.indicator_of_mem hy, abs_of_nonpos hy]
        ring
      · rw [Set.indicator_of_notMem hy, mul_zero, sub_zero,
          abs_of_pos (lt_of_not_ge hy)]
        ring
    _ = 0 - 2 * ∫ y in Set.Iic (0 : ℝ), y * standardGaussianPDF y := by
      rw [integral_sub integrable_id_mul_standardGaussianPDF
        ((integrable_id_mul_standardGaussianPDF.indicator measurableSet_Iic).const_mul 2),
        integral_const_mul, integral_indicator measurableSet_Iic, hmean]
    _ = 2 * standardGaussianPDF 0 := by
      rw [integral_Iic_id_mul_standardGaussianPDF]
      ring

/-- The scalar Gaussian rotation disagreement event is Borel measurable. -/
private lemma measurableSet_scalar_rotation_disagreement (t θ : ℝ) :
    MeasurableSet {z : ℝ × ℝ |
      ¬ (z.1 ≤ t ↔ Real.cos θ * z.1 + Real.sin θ * z.2 ≤ t)} := by
  have h₁ : MeasurableSet {z : ℝ × ℝ | z.1 ≤ t} :=
    measurableSet_le measurable_fst measurable_const
  have h₂ : MeasurableSet
      {z : ℝ × ℝ | Real.cos θ * z.1 + Real.sin θ * z.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  convert h₁.symmDiff h₂ using 1
  ext z
  simp only [ Set.mem_setOf_eq, Set.mem_symmDiff]
  tauto

/-- When the cosine is positive, scalar rotation disagreement is the integral
of absolute conditional Gaussian CDF increments.

**Proof sketch.** Condition on the second coordinate using the product-measure
formula. The two membership conditions become lower halflines in the first
coordinate; their symmetric difference has measure equal to the CDF increment. -/
private lemma scalar_rotation_disagreement_eq_integral (t θ : ℝ) (hcos : 0 < Real.cos θ) :
    (((standardGaussianMeasure.prod standardGaussianMeasure)
      {z : ℝ × ℝ | ¬ (z.1 ≤ t ↔ Real.cos θ * z.1 + Real.sin θ * z.2 ≤ t)}).toReal) =
      ∫ y, |standardGaussianCDF ((t - Real.sin θ * y) / Real.cos θ) - standardGaussianCDF t|
        ∂standardGaussianMeasure := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  let γ := standardGaussianMeasure
  let E : Set (ℝ × ℝ) :=
    {z | ¬ (z.1 ≤ t ↔ Real.cos θ * z.1 + Real.sin θ * z.2 ≤ t)}
  have hE : MeasurableSet E := measurableSet_scalar_rotation_disagreement t θ
  change ((γ.prod γ) E).toReal = _
  rw [Measure.prod_apply_symm hE,
    ← integral_toReal (measurable_measure_prodMk_right (μ := γ) hE).aemeasurable
      (Eventually.of_forall fun y => measure_lt_top γ _)]
  apply integral_congr_ae
  filter_upwards [] with y
  have hslice : (fun x : ℝ => (x, y)) ⁻¹' E =
      symmDiff (Set.Iic t) (Set.Iic ((t - Real.sin θ * y) / Real.cos θ)) := by
    ext x
    have hcut : Real.cos θ * x + Real.sin θ * y ≤ t ↔
        x ≤ (t - Real.sin θ * y) / Real.cos θ := by
      rw [le_div_iff₀ hcos]
      constructor <;> intro h <;> nlinarith
    simp only [Set.mem_preimage, E, Set.mem_setOf_eq, Set.mem_symmDiff,
      Set.mem_Iic, hcut]
    tauto
  change γ.real ((fun x : ℝ => (x, y)) ⁻¹' E) = _
  rw [hslice]
  exact standardGaussianMeasure_symmDiff_Iic t _

/-- The rotation-to-surface-area normalization cancels the first absolute
standard Gaussian moment. [OD14, Def. 11.48]

**Proof sketch.** Insert the Gaussian density at zero and cancel the positive
square-root factors. -/
lemma gaussian_surface_normalization :
    Real.sqrt (Real.pi / 2) * (2 * standardGaussianPDF 0) = 1 := by
  have hs : 2 * Real.sqrt (Real.pi / 2) = Real.sqrt (2 * Real.pi) := by
    calc
      _ = Real.sqrt (4 * (Real.pi / 2)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        rw [show Real.sqrt (4 : ℝ) = 2 from by
          simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
            Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
      _ = _ := by congr 1; ring
  simp only [standardGaussianPDF_eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, neg_zero, zero_div, Real.exp_zero, mul_one]
  calc
    _ = (2 * Real.sqrt (Real.pi / 2)) * (Real.sqrt (2 * Real.pi))⁻¹ := by ring
    _ = 1 := by rw [hs, mul_inv_cancel₀ (by positivity)]

/-- The normalized scalar rotation crossing quotient tends to the Gaussian
density at the threshold. [OD14, Prop. 11.49 (proof)]

**Proof sketch.** Use the conditional integral formula at small positive angles
and the established dominated-convergence limit. The Gaussian absolute moment
cancels the surface-area normalization. -/
private lemma scalar_rotation_disagreement_quotient_tendsto (t : ℝ) :
    Tendsto (fun θ : ℝ => Real.sqrt (Real.pi / 2) *
      (((standardGaussianMeasure.prod standardGaussianMeasure)
        {z : ℝ × ℝ | ¬ (z.1 ≤ t ↔ Real.cos θ * z.1 + Real.sin θ * z.2 ≤ t)}).toReal) / θ)
      (𝓝[>] (0 : ℝ)) (𝓝 (standardGaussianPDF t)) := by
  have h := (integral_rotated_gaussianCDF_quotient_tendsto t).const_mul (Real.sqrt (Real.pi / 2))
  rw [integral_abs_standardGaussian] at h
  have hn : Real.sqrt (Real.pi / 2) * (standardGaussianPDF t * (2 * standardGaussianPDF 0)) =
      standardGaussianPDF t := by
    calc
      _ = standardGaussianPDF t * (Real.sqrt (Real.pi / 2) * (2 * standardGaussianPDF 0)) := by ring
      _ = _ := by rw [gaussian_surface_normalization, mul_one]
  rw [hn] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
  have hcos : 0 < Real.cos θ := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := θ), sq_nonneg (1 - θ), hθ.1, hθ.2]
  rw [scalar_rotation_disagreement_eq_integral t θ hcos, integral_div]
  ring

/-- Rotation sensitivity of a unit-normal halfspace equals the corresponding
one-dimensional Gaussian crossing probability. [OD14, Prop. 11.49 (proof)]

**Proof sketch.** Apply the unit Gaussian projection independently to both
vectors in the coupling. The projected linear combination commutes with
rotation, so the disagreement event is the preimage of the scalar event. -/
lemma rotationSensitivity_halfspace_eq_scalar {n : ℕ} (a : Fin n → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (t θ : ℝ) :
    rotationSensitivity {z : Fin n → ℝ | ∑ i, a i * z i ≤ t} θ =
      (((standardGaussianMeasure.prod standardGaussianMeasure)
        {z : ℝ × ℝ | ¬ (z.1 ≤ t ↔ Real.cos θ * z.1 + Real.sin θ * z.2 ≤ t)}).toReal) := by
  letI : IsProbabilityMeasure standardGaussianMeasure := by
    unfold standardGaussianMeasure
    infer_instance
  let E : Set (ℝ × ℝ) :=
    {z | ¬ (z.1 ≤ t ↔ Real.cos θ * z.1 + Real.sin θ * z.2 ≤ t)}
  have hE : MeasurableSet E := measurableSet_scalar_rotation_disagreement t θ
  have hlin (z w : Fin n → ℝ) :
      (∑ i, a i * (Real.cos θ * z i + Real.sin θ * w i)) =
        Real.cos θ * (∑ i, a i * z i) + Real.sin θ * (∑ i, a i * w i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hp := (measurePreserving_gaussianProjection a ha).prod
    (measurePreserving_gaussianProjection a ha)
  unfold rotationSensitivity
  apply congrArg ENNReal.toReal
  rw [← hp.measure_preimage hE.nullMeasurableSet]
  congr 1
  ext z
  change (¬ ((∑ i, a i * z.1 i) ≤ t ↔
      (∑ i, a i * (Real.cos θ * z.1 i + Real.sin θ * z.2 i)) ≤ t)) ↔
    (¬ ((∑ i, a i * z.1 i) ≤ t ↔
      Real.cos θ * (∑ i, a i * z.1 i) +
        Real.sin θ * (∑ i, a i * z.2 i) ≤ t))
  rw [hlin]

/-- The normalized rotation-sensitivity quotient of a unit-normal halfspace
tends to the Gaussian density at its threshold. [OD14, Prop. 11.49]

**Proof sketch.** Project the two Gaussian vectors onto the unit normal and
apply the scalar crossing-probability limit. -/
lemma halfspace_rotation_quotient_tendsto {n : ℕ} (a : Fin n → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (t : ℝ) :
    Tendsto (fun θ : ℝ => Real.sqrt (Real.pi / 2) *
      rotationSensitivity {z : Fin n → ℝ | ∑ i, a i * z i ≤ t} θ / θ)
      (𝓝[>] (0 : ℝ)) (𝓝 (standardGaussianPDF t)) := by
  simpa only [rotationSensitivity_halfspace_eq_scalar a ha t] using
    scalar_rotation_disagreement_quotient_tendsto t


/-- The first absolute moment of a Gaussian linear combination is its Euclidean
coefficient length times the first absolute standard Gaussian moment.

**Proof sketch.** If the squared coefficient length is zero, every coefficient
vanishes. Otherwise normalize the coefficients to a unit vector, apply the
Gaussian projection law, and rescale the known scalar absolute moment. -/
lemma integral_abs_gaussianProjection {n : ℕ} (a : Fin n → ℝ) :
    (∫ z : Fin n → ℝ, |∑ i, a i * z i|
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) =
      Real.sqrt (∑ i, a i ^ 2) * (2 * standardGaussianPDF 0) := by
  have hnonneg : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases eq_or_lt_of_le hnonneg with hs | hs
  · have ha (i : Fin n) : a i = 0 := by
      apply sq_eq_zero_iff.mp
      apply le_antisymm _ (sq_nonneg _)
      have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (a j))
        (Finset.mem_univ i)
      linarith
    simp [ha]
  · let r := Real.sqrt (∑ i, a i ^ 2)
    have hr : 0 < r := Real.sqrt_pos.mpr hs
    have hr2 : r ^ 2 = ∑ i, a i ^ 2 := Real.sq_sqrt hnonneg
    have hb : ∑ i, (a i / r) ^ 2 = 1 := by
      simp_rw [div_pow]
      rw [← Finset.sum_div, hr2, div_self hs.ne']
    have hp := measurePreserving_gaussianProjection (fun i => a i / r) hb
    have hi := integral_map_of_stronglyMeasurable
      (μ := Measure.pi fun _ : Fin n => standardGaussianMeasure) hp.measurable
      (show StronglyMeasurable (fun x : ℝ => |x|) from continuous_abs.stronglyMeasurable)
    rw [hp.map_eq] at hi
    have hsum (z : Fin n → ℝ) : ∑ i, a i * z i = r * ∑ i, (a i / r) * z i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    calc
      _ = ∫ z : Fin n → ℝ, r * |∑ i, (a i / r) * z i|
          ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          dsimp only
          rw [hsum, abs_mul, abs_of_pos hr]
      _ = r * ∫ z : Fin n → ℝ, |∑ i, (a i / r) * z i|
          ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure) := integral_const_mul _ _
      _ = _ := by rw [← hi, integral_abs_standardGaussian]


end BooleanAnalysis.GaussianSpace
