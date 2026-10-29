/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.NoiseDefinitions
import TCSlib.BooleanAnalysis.GaussianSpace.ProductDensity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Gaussian noise kernel density bounds

## Main definitions

The existing real Gaussian densities and finite product laws are reused.

## Main results

* `gaussianPDFReal_noise_le`: a noise kernel density is bounded by a finite
  multiple of the standard Gaussian density at every fixed starting point.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.1, Definition 11.12 and Proposition 11.16.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

local instance : IsProbabilityMeasure standardGaussianMeasure :=
  inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

/-- At a fixed starting point, the scalar noise density is dominated by a
finite multiple of the standard Gaussian density.
[OD14, §11.1, Gaussian noise kernel]

**Proof sketch.** The exponent comparison is the nonnegativity of
`(ρz-x)²`, using `v+ρ²=1`. Compare the exponential factors and keep the
positive normalization factors explicit. -/
lemma gaussianPDFReal_noise_le (ρ x z : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (hvar : (v : ℝ) + ρ ^ 2 = 1) :
    gaussianPDFReal (ρ * x) v z ≤
      (Real.sqrt (2 * Real.pi) / Real.sqrt (2 * Real.pi * v) * Real.exp (x ^ 2 / 2)) *
        gaussianPDFReal 0 1 z := by
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have he : -(z - ρ * x) ^ 2 / (2 * (v : ℝ)) ≤ x ^ 2 / 2 - z ^ 2 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (v : ℝ))).2
    nlinarith [sq_nonneg (ρ * z - x),
      congrArg (fun t : ℝ => t * x ^ 2) hvar,
      congrArg (fun t : ℝ => t * z ^ 2) hvar]
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  calc
    _ ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ *
        Real.exp (x ^ 2 / 2 - z ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add]
      field_simp

/-- A finite Gaussian noise kernel is bounded by a finite scalar multiple of
the standard Gaussian product law at every fixed starting point.
[OD14, §11.1, Gaussian noise kernel]

**Proof sketch.** Multiply the scalar density bounds over the coordinates,
then compare the two measures through their existing product densities. -/
lemma pi_gaussianNoise_le_smul {n : ℕ} (ρ : ℝ) (x : Fin n → ℝ)
    (v : ℝ≥0) (hv : v ≠ 0) (hvar : (v : ℝ) + ρ ^ 2 = 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      (Measure.pi fun i => gaussianReal (ρ * x i) v) ≤
        C • (Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  let K := fun i : Fin n => Real.sqrt (2 * Real.pi) /
    Real.sqrt (2 * Real.pi * v) * Real.exp (x i ^ 2 / 2)
  have hK (i : Fin n) : 0 ≤ K i := by dsimp [K]; positivity
  let C := ENNReal.ofReal (∏ i, K i)
  refine ⟨C, ENNReal.ofReal_ne_top, ?_⟩
  change (Measure.pi fun i => gaussianReal (ρ * x i) v) ≤
    C • (Measure.pi fun _ : Fin n => gaussianReal 0 1)
  rw [pi_gaussianReal_eq_withDensity _ v hv,
    pi_gaussianReal_eq_withDensity (fun _ : Fin n => 0) 1 (by norm_num),
    ← withDensity_smul' C _ ENNReal.ofReal_ne_top]
  apply withDensity_mono
  filter_upwards [] with z
  change ENNReal.ofReal (∏ i, gaussianPDFReal (ρ * x i) v (z i)) ≤
    C * ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (z i))
  dsimp [C]
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hK i)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∏ i, K i * gaussianPDFReal 0 1 (z i) :=
      Finset.prod_le_prod (fun i _ => gaussianPDFReal_nonneg _ _ _)
        (fun i _ => gaussianPDFReal_noise_le ρ (x i) (z i) v hv hvar)
    _ = _ := Finset.prod_mul_distrib

/-- Every section of a valid Gaussian noise kernel is integrable for a Gaussian
integrable input. [OD14, §11.1, Gaussian noise kernel]

**Proof sketch.** A zero noise coefficient gives a constant integrand. Otherwise,
the affine Gaussian law is bounded by a finite multiple of the standard law.
Transfer integrability through this domination and the affine pushforward. -/
lemma integrable_gaussianNoise_integrand {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) {f : (Fin n → ℝ) → ℝ}
    (hf : Integrable f (Measure.pi fun _ : Fin n => standardGaussianMeasure))
    (x : Fin n → ℝ) :
    Integrable (fun y => f (fun i => ρ * x i + Real.sqrt (1 - ρ ^ 2) * y i))
      (Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  let s := Real.sqrt (1 - ρ ^ 2)
  change Integrable (fun y : Fin n → ℝ => f (fun i => ρ * x i + s * y i)) _
  by_cases hs : s = 0
  · simp only [hs, zero_mul, add_zero]
    exact integrable_const _
  · let v : ℝ≥0 := ⟨s ^ 2, sq_nonneg s⟩
    have hv : v ≠ 0 := by
      intro h
      exact hs (eq_zero_of_pow_eq_zero (congrArg (fun t : ℝ≥0 => (t : ℝ)) h))
    have hvar : (v : ℝ) + ρ ^ 2 = 1 := by
      dsimp [v, s]
      rw [Real.sq_sqrt (show 0 ≤ 1 - ρ ^ 2 by nlinarith [hρ.1, hρ.2])]
      ring
    obtain ⟨C, hC, hbound⟩ := pi_gaussianNoise_le_smul ρ x v hv hvar
    exact (measurePreserving_gaussianAffine_pi (fun i => ρ * x i) s).integrable_comp_of_integrable
      ((hf.smul_measure hC).mono_measure hbound)

/-- The Gaussian noise density relative to the standard Gaussian factors into a
smooth starting-point factor and a translated Gaussian exponential.
[OD14, Prop. 11.16, Gaussian kernel]

**Proof sketch.** Complete the square in the exponent using `v+ρ²=1`.
Factor the exponential and keep the density normalizations explicit. -/
lemma gaussianPDFReal_noise_eq (ρ x z : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (hvar : (v : ℝ) + ρ ^ 2 = 1) :
    gaussianPDFReal (ρ * x) v z =
      (Real.sqrt (2 * Real.pi) / Real.sqrt (2 * Real.pi * v) * Real.exp (x ^ 2 / 2) *
        Real.exp (-(ρ * z - x) ^ 2 / (2 * v))) * gaussianPDFReal 0 1 z := by
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have he : -(z - ρ * x) ^ 2 / (2 * (v : ℝ)) =
      x ^ 2 / 2 - (ρ * z - x) ^ 2 / (2 * (v : ℝ)) - z ^ 2 / 2 := by
    field_simp [ne_of_gt hvpos]
    nlinarith [congrArg (fun t : ℝ => t * x ^ 2) hvar,
      congrArg (fun t : ℝ => t * z ^ 2) hvar]
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [he]
  simp only [sub_eq_add_neg, Real.exp_add, neg_div]
  field_simp

/-- Rescaling the Gaussian exponent expresses it as the squared Fourier
coefficient norm. -/
lemma gaussianNoise_exponent_sum {n : ℕ} (ρ s : ℝ) (hs : s ≠ 0)
    (x y : Fin n → ℝ) :
    (∑ i, -(ρ * y i - x i) ^ 2 / (2 * s ^ 2)) =
      -(∑ i, ((1 / s) * x i + (-ρ / s) * y i) ^ 2) / 2 := by
  calc
    _ = ∑ i, -((1 / s) * x i + (-ρ / s) * y i) ^ 2 / 2 := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp
      ring
    _ = _ := by rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

/-- The finite product noise density factors into a smooth translation factor,
a Gaussian exponential kernel, and the standard product density.
[OD14, Prop. 11.16, Gaussian kernel]

**Proof sketch.** Multiply the scalar completed-square identity over all
coordinates and combine the exponential factors by summing their exponents. -/
lemma gaussianProductDensity_noise_eq {n : ℕ} (ρ s : ℝ) (hs : s ≠ 0)
    (hvar : s ^ 2 + ρ ^ 2 = 1) (x y : Fin n → ℝ) :
    (∏ i, gaussianPDFReal (ρ * x i) ⟨s ^ 2, sq_nonneg s⟩ (y i)) =
      (Real.sqrt (2 * Real.pi) / Real.sqrt (2 * Real.pi * s ^ 2)) ^ n *
        Real.exp ((∑ i, x i ^ 2) / 2) *
        Real.exp (-(∑ i, ((1 / s) * x i + (-ρ / s) * y i) ^ 2) / 2) *
        ∏ i, gaussianPDFReal 0 1 (y i) := by
  have hv : (⟨s ^ 2, sq_nonneg s⟩ : ℝ≥0) ≠ 0 := by
    intro h
    exact pow_ne_zero 2 hs (congrArg Subtype.val h)
  calc
    _ = ∏ i, (Real.sqrt (2 * Real.pi) / Real.sqrt (2 * Real.pi * s ^ 2) *
        Real.exp (x i ^ 2 / 2) * Real.exp (-(ρ * y i - x i) ^ 2 / (2 * s ^ 2))) *
        gaussianPDFReal 0 1 (y i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact gaussianPDFReal_noise_eq ρ (x i) (y i) _ hv hvar
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← Real.exp_sum]
      rw [gaussianNoise_exponent_sum ρ s hs x y, ← Finset.sum_div]

/-- An affine Gaussian average factors into a smooth function of the starting
point times a Gaussian exponential average against the standard law.
[OD14, Prop. 11.16, Gaussian kernel]

**Proof sketch.** The nonzero affine map is a measurable embedding, so its
pushforward integral formula applies to arbitrary representatives. Write the
affine law using its product density, apply the completed-square factorization,
and recognize the standard Gaussian density in the remaining integral. -/
lemma integral_gaussianNoise_densityFactorization {n : ℕ} (ρ s : ℝ) (hs : s ≠ 0)
    (hvar : s ^ 2 + ρ ^ 2 = 1) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    (∫ y, f (fun i => ρ * x i + s * y i)
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) =
      ((Real.sqrt (2 * Real.pi) / Real.sqrt (2 * Real.pi * s ^ 2)) ^ n *
        Real.exp ((∑ i, x i ^ 2) / 2)) *
      ∫ y, f y * Real.exp (-(∑ i, ((1 / s) * x i + (-ρ / s) * y i) ^ 2) / 2)
        ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure) := by
  let K := (Real.sqrt (2 * Real.pi) / Real.sqrt (2 * Real.pi * s ^ 2)) ^ n *
    Real.exp ((∑ i, x i ^ 2) / 2)
  have hv : (⟨s ^ 2, sq_nonneg s⟩ : ℝ≥0) ≠ 0 := by
    intro h
    exact pow_ne_zero 2 hs (congrArg Subtype.val h)
  have hp := measurePreserving_gaussianAffine_pi (fun i => ρ * x i) s
  have hm : MeasurableEmbedding (fun y : Fin n → ℝ => fun i => ρ * x i + s * y i) :=
    (measurableEmbedding_addLeft (fun i => ρ * x i)).comp
      (measurableEmbedding_const_smul₀ hs)
  change _ = K * _
  calc
    _ = ∫ z, f z ∂(Measure.pi fun i => gaussianReal (ρ * x i) ⟨s ^ 2, sq_nonneg s⟩) := by
      conv_rhs => rw [← hp.map_eq]
      exact (hm.integral_map f).symm
    _ = ∫ y, (∏ i, gaussianPDFReal (ρ * x i) ⟨s ^ 2, sq_nonneg s⟩ (y i)) * f y
        ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
      integral_pi_gaussianReal_eq_integral_smul _ _ hv f
    _ = K * ∫ y, (∏ i, gaussianPDFReal 0 1 (y i)) *
        (f y * Real.exp (-(∑ i, ((1 / s) * x i + (-ρ / s) * y i) ^ 2) / 2))
          ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [gaussianProductDensity_noise_eq ρ s hs hvar]
      dsimp [K]
      ring
    _ = _ := by
      congr 1
      exact (integral_pi_gaussianReal_eq_integral_smul (fun _ : Fin n => 0) 1
        (by norm_num) _).symm

end BooleanAnalysis.GaussianSpace
