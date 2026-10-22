/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Invariance
import TCSlib.BooleanAnalysis.GaussianSpace.SumInvariance
import TCSlib.BooleanAnalysis.GaussianSpace.Invariance.Cutoff

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Distributional comparison from smooth tests

## Main definitions

The existing one-dimensional Lévy distance and interval averaging are reused.

## Main results

Smooth expectation estimates imply Lévy bounds by comparison with half-line cutoffs.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, Corollary 11.70.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BooleanAnalysis.GaussianSpace.Invariance

open ThresholdFunctions Hypercontractivity

/-- Any nonnegative shift satisfying the CDF sandwich bounds the Lévy distance.
[OD14, §11.5, definition of Lévy distance] -/
lemma levyDistance_le_of_cdf (μ ν : Measure ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ u : ℝ,
      (ν (Set.Iic (u - ε))).toReal - ε ≤ (μ (Set.Iic u)).toReal ∧
        (μ (Set.Iic u)).toReal ≤ (ν (Set.Iic (u + ε))).toReal + ε) :
    levyDistance μ ν ≤ ε := by
  apply csInf_le ⟨0, fun r hr => hr.1⟩
  exact ⟨hε, h⟩

/-- Bidirectional CDF comparisons with horizontal error `w` and vertical error
`e` bound the Lévy distance by `w + e`. [OD14, §11.5, CDF comparison]

**Proof sketch.** Enlarge the horizontal shift to `w + e` using monotonicity of
the CDFs. The reverse comparison supplies the lower half of the sandwich. -/
lemma levyDistance_le_of_cdf_comparison (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {w e : ℝ} (hw : 0 ≤ w) (he : 0 ≤ e)
    (h : ∀ u, (μ (Set.Iic u)).toReal ≤ (ν (Set.Iic (u + w))).toReal + e ∧
      (ν (Set.Iic u)).toReal ≤ (μ (Set.Iic (u + w))).toReal + e) :
    levyDistance μ ν ≤ w + e := by
  apply levyDistance_le_of_cdf μ ν (add_nonneg hw he)
  intro u
  constructor
  · have hreverse := (h (u - (w + e))).2
    have hmono : (μ (Set.Iic (u - (w + e) + w))).toReal ≤ (μ (Set.Iic u)).toReal :=
      measureReal_mono (Set.Iic_subset_Iic.mpr (by linarith))
    linarith
  · have hmono : (ν (Set.Iic (u + w))).toReal ≤ (ν (Set.Iic (u + (w + e)))).toReal :=
      measureReal_mono (Set.Iic_subset_Iic.mpr (by linarith))
    linarith [(h u).1]

/-- The integral of a bounded half-line cutoff lies between the CDF values at
its two constant regions. [OD14, Cor. 11.70 (proof)]

**Proof sketch.** Compare the cutoff pointwise with the two half-line indicators.
Boundedness supplies integrability, and the indicator integrals are the CDF values. -/
lemma integral_cutoff_sandwich (μ : Measure ℝ) [IsFiniteMeasure μ]
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hrange : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1)
    {u v : ℝ} (hone : ∀ x, x ≤ u → φ x = 1) (hzero : ∀ x, v ≤ x → φ x = 0) :
    (μ (Set.Iic u)).toReal ≤ ∫ x, φ x ∂μ ∧
      (∫ x, φ x ∂μ) ≤ (μ (Set.Iic v)).toReal := by
  have hInt : Integrable φ μ :=
    Integrable.of_bound hφ.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hrange x).1]
        exact (hrange x).2)
  constructor
  · calc
      _ = ∫ x, (Set.Iic u).indicator (1 : ℝ → ℝ) x ∂μ :=
        (integral_indicator_one measurableSet_Iic).symm
      _ ≤ _ := integral_mono
        ((integrable_const (1 : ℝ)).indicator measurableSet_Iic) hInt
        (fun x => by
          simp only [Set.indicator_apply, Set.mem_Iic, Pi.one_apply]
          split_ifs with hx
          · rw [hone x hx]
          · exact (hrange x).1)
  · calc
      _ ≤ ∫ x, (Set.Iic v).indicator (1 : ℝ → ℝ) x ∂μ :=
        integral_mono hInt
          ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
          (fun x => by
            simp only [Set.indicator_apply, Set.mem_Iic, Pi.one_apply]
            split_ifs with hx
            · exact (hrange x).2
            · rw [hzero x (le_of_lt (lt_of_not_ge hx))])
      _ = _ := integral_indicator_one measurableSet_Iic

/-- A derivative-based expectation comparison bounds the Lévy distance at any
positive smoothing scale. [OD14, Cor. 11.70 (proof)]

**Proof sketch.** Insert a smooth cutoff between the two CDF values separated by
its transition width. The smooth-test estimate controls its expectation difference.
Apply the CDF comparison in both directions and add the horizontal and vertical errors. -/
theorem levy_bound_at_scale (m : ℕ) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ (φ : ℝ → ℝ), ContDiff ℝ (m + 1 : ℕ) φ →
      ∀ C : ℝ, 0 ≤ C → (∀ t, |iteratedDeriv (m + 1) φ t| ≤ C) →
        |(∫ x, φ x ∂μ) - ∫ x, φ x ∂ν| ≤ C * B)
    (η : ℝ) (hη : 0 < η) :
    levyDistance μ ν ≤ ((m + 2 : ℕ) : ℝ) * η +
      ((2 : ℝ) ^ m / η ^ (m + 1)) * B := by
  apply levyDistance_le_of_cdf_comparison μ ν (by positivity) (by positivity)
  intro u
  obtain ⟨φ, hφ, hrange, hone, hzero, hderiv⟩ := exists_contDiff_cutoff m u hη
  obtain ⟨hμlo, hμhi⟩ := integral_cutoff_sandwich μ hφ.continuous hrange hone hzero
  obtain ⟨hνlo, hνhi⟩ := integral_cutoff_sandwich ν hφ.continuous hrange hone hzero
  have hdiff := abs_le.mp (herror φ hφ ((2 : ℝ) ^ m / η ^ (m + 1))
    (by positivity) hderiv)
  constructor <;> linarith [hdiff.1, hdiff.2]

/-- Balancing a linear smoothing error against an inverse-power error gives
the corresponding fractional-power bound. [OD14, Cor. 11.70 (proof)]

**Proof sketch.** For positive error budget, use its `(m+2)`nd root as the scale.
For zero budget, let an arbitrary positive scale tend to zero. -/
theorem levy_bound_of_scale
    (m : ℕ) {L B : ℝ} (hB : 0 ≤ B)
    (hscale : ∀ η : ℝ, 0 < η →
      L ≤ ((m + 2 : ℕ) : ℝ) * η + ((2 : ℝ) ^ m / η ^ (m + 1)) * B) :
    L ≤ (((m + 2 : ℕ) : ℝ) + (2 : ℝ) ^ m) *
      B ^ (1 / ((m + 2 : ℕ) : ℝ)) := by
  rcases eq_or_lt_of_le hB with rfl | hBpos
  · simp only [Real.zero_rpow (by positivity : (1 / ((m + 2 : ℕ) : ℝ)) ≠ 0), mul_zero]
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hA : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
    have hη : 0 < δ / ((m + 2 : ℕ) : ℝ) := div_pos hδ hA
    have h := hscale _ hη
    simp only [mul_zero, add_zero] at h
    have heq : ((m + 2 : ℕ) : ℝ) * (δ / ((m + 2 : ℕ) : ℝ)) = δ := by
      field_simp
    simpa only [heq, zero_add] using h
  · let η := B ^ (1 / ((m + 2 : ℕ) : ℝ))
    have hη : 0 < η := Real.rpow_pos_of_pos hBpos _
    have hpow : η ^ (m + 2) = B := by
      simpa only [η, one_div] using
        Real.rpow_inv_natCast_pow hB (by omega : m + 2 ≠ 0)
    calc
      _ ≤ ((m + 2 : ℕ) : ℝ) * η + ((2 : ℝ) ^ m / η ^ (m + 1)) * B :=
        hscale η hη
      _ = _ := by
        change ((m + 2 : ℕ) : ℝ) * η + ((2 : ℝ) ^ m / η ^ (m + 1)) * B =
          (((m + 2 : ℕ) : ℝ) + (2 : ℝ) ^ m) * η
        rw [← hpow, show m + 2 = (m + 1) + 1 by omega, pow_succ]
        field_simp
        ring

/-- A comparison using bounded derivatives of order `m+1` gives a Lévy bound
with exponent `1/(m+2)`. [OD14, §11.5, Cor. 11.61; §11.6, Cor. 11.70] -/
theorem levy_bound_of_derivative (m : ℕ) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ (φ : ℝ → ℝ), ContDiff ℝ (m + 1 : ℕ) φ →
      ∀ C : ℝ, 0 ≤ C → (∀ t, |iteratedDeriv (m + 1) φ t| ≤ C) →
        |(∫ x, φ x ∂μ) - ∫ x, φ x ∂ν| ≤ C * B) :
    levyDistance μ ν ≤ (((m + 2 : ℕ) : ℝ) + (2 : ℝ) ^ m) *
      B ^ (1 / ((m + 2 : ℕ) : ℝ)) :=
  levy_bound_of_scale m hB (levy_bound_at_scale m μ ν B hB herror)

/-- A smooth-test comparison of real random variables gives the same Lévy
bound for their output laws. [OD14, Cor. 11.70 (proof)] -/
theorem levy_bound_of_derivative_map (m : ℕ)
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {U : Ω → ℝ} {V : Ξ → ℝ} (hU : AEMeasurable U μ) (hV : AEMeasurable V ν)
    (B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ (φ : ℝ → ℝ), ContDiff ℝ (m + 1 : ℕ) φ →
      ∀ C : ℝ, 0 ≤ C → (∀ t, |iteratedDeriv (m + 1) φ t| ≤ C) →
        |(∫ ω, φ (U ω) ∂μ) - ∫ ω, φ (V ω) ∂ν| ≤ C * B) :
    levyDistance (μ.map U) (ν.map V) ≤ (((m + 2 : ℕ) : ℝ) + (2 : ℝ) ^ m) *
      B ^ (1 / ((m + 2 : ℕ) : ℝ)) := by
  haveI := Measure.isProbabilityMeasure_map hU
  haveI := Measure.isProbabilityMeasure_map hV
  apply levy_bound_of_derivative m (μ.map U) (ν.map V) B hB
  intro φ hφ C hC0 hC
  rw [integral_map hU hφ.continuous.aestronglyMeasurable,
    integral_map hV hφ.continuous.aestronglyMeasurable]
  exact herror φ hφ C hC0 hC

/-- The fifth root of the fourth-order invariance scale is at most `2^k` times
the fifth root of the influence bound. [OD14, Cor. 11.70 (proof)]

**Proof sketch.** Bound the degree factor by `32^k` using the stronger existing
`16^k` estimate, then take fifth roots and factor the product. -/
lemma invariance_fifth_power_le (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ((k : ℝ) * (9 : ℝ) ^ k * ε / 12) ^ (1 / 5 : ℝ) ≤
      (2 : ℝ) ^ k * ε ^ (1 / 5 : ℝ) := by
  have hdegree : (k : ℝ) * (9 : ℝ) ^ k ≤ (32 : ℝ) ^ k :=
    (degree_mul_nine_pow_le_sixteen_pow k).trans
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (16 : ℝ) ≤ 32) k)
  have hscale : 0 ≤ (k : ℝ) * (9 : ℝ) ^ k * ε := by positivity
  calc
    _ ≤ ((32 : ℝ) ^ k * ε) ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow (div_nonneg hscale (by norm_num))
        ((div_le_self hscale (by norm_num : (1 : ℝ) ≤ 12)).trans
          (mul_le_mul_of_nonneg_right hdegree hε)) (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) hε,
        ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 32) _ k]
      have hroot : (32 : ℝ) ^ (1 / 5 : ℝ) = 2 := by
        rw [show (32 : ℝ) = 2 ^ 5 by norm_num]
        simpa only [one_div] using
          Real.pow_rpow_inv_natCast (x := (2 : ℝ)) (n := 5) (by norm_num) (by norm_num)
      rw [hroot]

/-- A reciprocal hypercontractive radius bounded below by `6/5` absorbs the
third-order degree factor after taking fourth roots. [OD14, Cor. 11.70 (proof)]

**Proof sketch.** Bound `k` by `2^k` and then by `r^(4k)`. The remaining radius
powers are at most `r^(8k)`; its fourth root is `r^(2k)`, while the square-root
influence factor becomes the eighth root. -/
lemma invariance_c3_quarter_power_le (k : ℕ) {r ε : ℝ}
    (hr : (6 / 5 : ℝ) ≤ r) (hε : 0 ≤ ε) :
    ((k : ℝ) * r ^ (3 * k) * Real.sqrt ε / 3) ^ (1 / 4 : ℝ) ≤
      r ^ (2 * k) * ε ^ (1 / 8 : ℝ) := by
  have hr1 : 1 ≤ r := (by norm_num : (1 : ℝ) ≤ 6 / 5).trans hr
  have hr0 : 0 ≤ r := zero_le_one.trans hr1
  have htwo : (2 : ℝ) ≤ r ^ 4 :=
    (by norm_num : (2 : ℝ) ≤ (6 / 5 : ℝ) ^ 4).trans
      (pow_le_pow_left₀ (by norm_num) hr 4)
  have hk : (k : ℝ) ≤ r ^ (4 * k) := by
    calc
      (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast k.lt_two_pow_self.le
      _ ≤ (r ^ 4) ^ k := pow_le_pow_left₀ (by norm_num) htwo k
      _ = _ := by rw [← pow_mul]
  have hdegree : (k : ℝ) * r ^ (3 * k) / 3 ≤ r ^ (8 * k) := by
    calc
      _ ≤ (k : ℝ) * r ^ (3 * k) := div_le_self (by positivity) (by norm_num)
      _ ≤ r ^ (4 * k) * r ^ (3 * k) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
      _ = r ^ (4 * k + 3 * k) := (pow_add _ _ _).symm
      _ ≤ r ^ (8 * k) := pow_le_pow_right₀ hr1 (by omega)
  calc
    _ ≤ (r ^ (8 * k) * ε ^ (1 / 2 : ℝ)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by
        calc
          _ = ((k : ℝ) * r ^ (3 * k) / 3) * ε ^ (1 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hdegree (by positivity)) (by norm_num)
    _ = ((r ^ (2 * k)) ^ 4 * ε ^ (1 / 2 : ℝ)) ^ (1 / 4 : ℝ) := by
      rw [show 8 * k = 2 * k * 4 by omega, pow_mul]
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      · simpa only [one_div] using
          Real.pow_rpow_inv_natCast (x := r ^ (2 * k)) (n := 4) (by positivity) (by norm_num)
      · rw [← Real.rpow_mul hε]
        norm_num

end BooleanAnalysis.GaussianSpace.Invariance
