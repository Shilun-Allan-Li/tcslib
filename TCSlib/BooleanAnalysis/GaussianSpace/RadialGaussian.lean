/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TCSlib.BooleanAnalysis.GaussianSpace.ProductDensity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Radial integration of the standard Gaussian law

## Main definitions

The existing finite product Gaussian law and Euclidean norm are used.

## Main results

* `integral_gaussianPi_radial`: radial integration with the chi density.
* `radial_gaussian_weight_bounded`: boundedness of the polynomial Gaussian weight.
* `integrable_radial_gaussian_weight`: integrability of that weight.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Example 11.50 and Exercise 11.17.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace BooleanAnalysis.GaussianSpace

open ThresholdFunctions

/-- The product standard Gaussian density depends only on the Euclidean norm.
[OD14, §11.1, standard Gaussian product law]

**Proof sketch.** Multiply the scalar densities, combine exponentials, and
identify the sum of coordinate squares with the squared Euclidean norm. -/
lemma prod_standardGaussianPDF_eq_radial {n : ℕ} (x : Fin n → ℝ) :
    (∏ i, gaussianPDFReal 0 1 (x i)) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ n *
        Real.exp (-‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 / 2) := by
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

/-- The radial Gaussian normalization equals the chi-density normalization.

**Proof sketch.** Insert the volume of the Euclidean unit ball. The Gamma
recurrence cancels the dimension, and the powers of the Gaussian normalization
cancel the powers of pi. -/
private lemma radial_gaussian_constant {n : ℕ} (hn : 0 < n) :
    (Real.sqrt (2 * Real.pi))⁻¹ ^ n * (n : ℝ) *
      volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) =
    (2 : ℝ) ^ (1 - (n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [measureReal_def, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [Real.Gamma_add_one (by positivity : (n : ℝ) / 2 ≠ 0)]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
  rw [mul_inv_rev, mul_pow]
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  have hg : Real.Gamma ((n : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have htwo : (Real.sqrt 2) ^ n = (2 : ℝ) ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [inv_pow, inv_pow, htwo,
    Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  field_simp

/-- Integrating a function of a nonzero-dimensional standard Gaussian vector's
Euclidean norm equals integrating it against the chi density.
[OD14, Example 11.50; Exercise 11.17]

**Proof sketch.** Replace the Gaussian product law by its radial density,
transport Lebesgue measure to Euclidean space, and apply Mathlib's radial
Haar integration formula. The unit-ball volume gives the Gamma normalization.
Both sides use the totalized Bochner integral, so no integrability assumption
is required. -/
theorem integral_gaussianPi_radial {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) :
    (∫ x : Fin n → ℝ, f ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖
      ∂(Measure.pi fun _ : Fin n => standardGaussianMeasure)) =
    ((2 : ℝ) ^ (1 - (n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)) *
      ∫ r in Set.Ioi (0 : ℝ), r ^ (n - 1) * Real.exp (-r ^ 2 / 2) * f r := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← radial_gaussian_constant hn]
  simp_rw [standardGaussianMeasure_eq]
  rw [integral_pi_gaussianReal_eq_integral_smul (fun _ => 0) 1 one_ne_zero]
  simp_rw [prod_standardGaussianPDF_eq_radial, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]
  have ht := (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2 / 2) * f ‖x‖)
  change (Real.sqrt (2 * Real.pi))⁻¹ ^ n *
    (∫ x : Fin n → ℝ,
      Real.exp (-‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 / 2) *
        f ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖) = _
  rw [ht, integral_fun_norm_addHaar volume (fun r => Real.exp (-r ^ 2 / 2) * f r)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]

/-- A polynomial times the Gaussian radial factor is bounded on the
nonnegative real axis.

**Proof sketch.** Gaussian decay gives convergence to zero at infinity;
continuity bounds the remaining compact interval. -/
lemma radial_gaussian_weight_bounded (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, 0 ≤ r →
      |r ^ k * Real.exp (-r ^ 2 / 2)| ≤ M := by
  have hc : Continuous (fun r : ℝ => r ^ k * Real.exp (-r ^ 2 / 2)) := by fun_prop
  have ht : Tendsto (fun r : ℝ => r ^ k * Real.exp (-r ^ 2 / 2))
      atTop (𝓝 0) := by
    have h := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
      (by norm_num : (0 : ℝ) < 1/2) (k : ℝ)).tendsto_zero_of_tendsto
      (by simpa only [neg_mul] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 1/2))))
    convert h using 1
    funext r
    rw [Real.rpow_natCast]
    congr 2
    ring
  obtain ⟨a, ha⟩ := eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    (hc.continuousOn : ContinuousOn (fun r : ℝ => r ^ k *
      Real.exp (-r ^ 2 / 2)) (Set.Icc 0 (max a 0)))
  refine ⟨max 1 B, le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro r hr
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg hr _) (Real.exp_pos _).le)]
  by_cases hra : a ≤ r
  · exact (ha r hra).le.trans (le_max_left _ _)
  · exact (hB ⟨r, ⟨hr, (le_of_not_ge hra).trans (le_max_left _ _)⟩, rfl⟩).trans
      (le_max_right _ _)

/-- Every natural-power Gaussian radial weight is integrable on the real line.

**Proof sketch.** Specialize Mathlib's integrability theorem for real powers
times a Gaussian, using that a natural exponent is greater than minus one. -/
lemma integrable_radial_gaussian_weight (k : ℕ) :
    Integrable (fun r : ℝ => r ^ k * Real.exp (-r ^ 2 / 2)) := (by
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (by norm_num : (0 : ℝ) < 1/2)
    (s := (k : ℝ))
    (show (-1 : ℝ) < (k : ℝ) by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith)
  convert h using 1
  funext r
  rw [Real.rpow_natCast]
  congr 2
  ring
)

end BooleanAnalysis.GaussianSpace
