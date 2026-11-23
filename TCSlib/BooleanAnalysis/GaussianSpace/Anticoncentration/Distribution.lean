/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.InvarianceDistribution

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Distributional comparison using interval anticoncentration

CDF comparisons with a fixed horizontal shift imply Kolmogorov bounds when
the reference measure assigns little mass to intervals of that width.

## Main definitions

The existing Kolmogorov distance and real interval measures are reused.

## Main results

* `kolmogorovDistance_le_of_cdf_comparison`: remove a CDF shift using interval bounds.
* `kolmogorov_bound_at_scale`: smooth-test comparison at a prescribed scale.
* `bound_of_power_smoothing`: balance linear and inverse-power errors.
* `kolmogorov_bound_of_fourth_derivative`: obtain the exponent `1/(4k+1)`.

Interval anticoncentration is an explicit hypothesis; these results do not use
an unfinished Gaussian polynomial small-ball estimate.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.6, proof of Theorem 11.71.
-/

open MeasureTheory

namespace BooleanAnalysis.GaussianSpace.Invariance

open ThresholdFunctions

/-- CDF comparisons with horizontal error `w` and vertical error `e` give a
Kolmogorov bound when every reference interval of width `w` has mass at most `A`.
[OD14, §11.6, proof of Thm. 11.71]

**Proof sketch.** The forward comparison bounds the CDF difference by the
reference mass in `(u, u+w]` plus `e`. Apply the reverse comparison at `u-w`
to bound the opposite difference by the mass in `(u-w, u]` plus `e`.
Take the supremum of the absolute differences. -/
lemma kolmogorovDistance_le_of_cdf_comparison (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {w e A : ℝ} (hw : 0 ≤ w)
    (hcompare : ∀ u : ℝ,
      (μ (Set.Iic u)).toReal ≤ (ν (Set.Iic (u + w))).toReal + e ∧
      (ν (Set.Iic u)).toReal ≤ (μ (Set.Iic (u + w))).toReal + e)
    (hinterval : ∀ u : ℝ, (ν (Set.Ioc u (u + w))).toReal ≤ A) :
    kolmogorovDistance μ ν ≤ A + e := (by
  have hstep (u : ℝ) :
      (ν (Set.Iic (u + w))).toReal - (ν (Set.Iic u)).toReal ≤ A := by
    have hsub : Set.Iic u ⊆ Set.Iic (u + w) :=
      Set.Iic_subset_Iic.mpr (by linarith)
    change ν.real (Set.Iic (u + w)) - ν.real (Set.Iic u) ≤ A
    rw [← measureReal_diff (μ := ν) hsub measurableSet_Iic, Set.Iic_diff_Iic]
    exact hinterval u
  rw [kolmogorovDistance_eq]
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨u, rfl⟩
  apply abs_le.mpr
  constructor
  · have hreverse := (hcompare (u - w)).2
    have hsmall := hstep (u - w)
    have hcancel : u - w + w = u := sub_add_cancel _ _
    rw [hcancel] at hreverse hsmall
    linarith
  · have hforward := (hcompare u).1
    have hsmall := hstep u
    linarith
)


/-- Smooth-test comparison and an interval mass bound give a Kolmogorov bound
at any positive smoothing scale. [OD14, §11.6, proof of Thm. 11.71]

**Proof sketch.** Insert a smooth half-line cutoff whose transition width is
`(m+2)η`. Its derivative bound controls the difference of its expectations.
The integral sandwiches give CDF comparisons in both directions, and the
reference interval bound removes the horizontal shift. -/
theorem kolmogorov_bound_at_scale (m : ℕ) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (B : ℝ) (_hB : 0 ≤ B)
    (herror : ∀ (φ : ℝ → ℝ), ContDiff ℝ (m + 1 : ℕ) φ →
      ∀ C : ℝ, 0 ≤ C → (∀ t, |iteratedDeriv (m + 1) φ t| ≤ C) →
        |(∫ x, φ x ∂μ) - ∫ x, φ x ∂ν| ≤ C * B)
    (η : ℝ) (hη : 0 < η) (A : ℝ)
    (hinterval : ∀ u : ℝ,
      (ν (Set.Ioc u (u + ((m + 2 : ℕ) : ℝ) * η))).toReal ≤ A) :
    kolmogorovDistance μ ν ≤ A +
      ((2 : ℝ) ^ m / η ^ (m + 1)) * B := (by
  apply kolmogorovDistance_le_of_cdf_comparison μ ν (by positivity) _ hinterval
  intro u
  obtain ⟨φ, hφ, hrange, hone, hzero, hderiv⟩ := exists_contDiff_cutoff m u hη
  obtain ⟨hμlo, hμhi⟩ := integral_cutoff_sandwich μ hφ.continuous hrange hone hzero
  obtain ⟨hνlo, hνhi⟩ := integral_cutoff_sandwich ν hφ.continuous hrange hone hzero
  have hdiff := abs_le.mp (herror φ hφ ((2 : ℝ) ^ m / η ^ (m + 1))
    (by positivity) hderiv)
  constructor <;> linarith [hdiff.1, hdiff.2]
)


/-- A linear smoothing error balanced against an inverse natural power gives
a fractional-power bound. [OD14, §11.6, proof of Thm. 11.71]

**Proof sketch.** For positive `B`, choose `t = B^(1/(q+1))`; the identity
`t^(q+1) = B` makes the inverse-power term equal to `t`. For `B = 0`,
let positive `t` tend to zero. The argument also allows `q = 0`. -/
lemma bound_of_power_smoothing (q : ℕ) {L A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hscale : ∀ t : ℝ, 0 < t → L ≤ A * t + B / t ^ q) :
    L ≤ (A + 1) * B ^ (1 / ((q + 1 : ℕ) : ℝ)) := (by
  rcases eq_or_lt_of_le hB with rfl | hBpos
  · simp only [Real.zero_rpow (by positivity :
      (1 / ((q + 1 : ℕ) : ℝ)) ≠ 0), mul_zero]
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hA1 : 0 < A + 1 := by positivity
    have ht : 0 < δ / (A + 1) := div_pos hδ hA1
    calc
      L ≤ A * (δ / (A + 1)) := by
        simpa only [zero_div, add_zero] using hscale _ ht
      _ ≤ (A + 1) * (δ / (A + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) ht.le
      _ = 0 + δ := by field_simp; ring
  · let t := B ^ (1 / ((q + 1 : ℕ) : ℝ))
    have ht : 0 < t := Real.rpow_pos_of_pos hBpos _
    have hpow : t ^ (q + 1) = B := by
      simpa only [t, one_div] using
        Real.rpow_inv_natCast_pow hB (by omega : q + 1 ≠ 0)
    calc
      L ≤ A * t + B / t ^ q := hscale t ht
      _ = (A + 1) * t := by
        rw [← hpow, pow_succ]
        field_simp
)


/-- Fourth-order smooth-test comparison and a power bound on reference
interval masses give a Kolmogorov estimate with exponent `1/(4k+1)`.
[OD14, §11.6, proof of Thm. 11.71]

**Proof sketch.** Apply the smooth cutoff estimate at scale `η = t^k`.
The transition width is `5η`, so the interval contribution is
`A * 5^(1/k) * t`, while the derivative contribution is `8B / t^(4k)`.
Balance these terms using the positive `(4k+1)`st root of `8B`;
the zero-budget case follows from the same general balancing lemma. -/
theorem kolmogorov_bound_of_fourth_derivative (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (k : ℕ) (hk : 1 ≤ k) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (herror : ∀ (φ : ℝ → ℝ), ContDiff ℝ (4 : ℕ) φ →
      ∀ C : ℝ, 0 ≤ C → (∀ t, |iteratedDeriv 4 φ t| ≤ C) →
        |(∫ x, φ x ∂μ) - ∫ x, φ x ∂ν| ≤ C * B)
    (hinterval : ∀ w : ℝ, 0 < w → ∀ u : ℝ,
      (ν (Set.Ioc u (u + w))).toReal ≤ A * w ^ (1 / (k : ℝ))) :
    kolmogorovDistance μ ν ≤
      (A * (5 : ℝ) ^ (1 / (k : ℝ)) + 1) *
        (8 * B) ^ (1 / ((4 * k + 1 : ℕ) : ℝ)) := (by
  apply bound_of_power_smoothing (4 * k) (by positivity) (by positivity)
  intro t ht
  have hroot : (t ^ k) ^ (1 / (k : ℝ)) = t := by
    simpa only [one_div] using
      Real.pow_rpow_inv_natCast ht.le (by omega : k ≠ 0)
  have hwidth : (5 * t ^ k) ^ (1 / (k : ℝ)) =
      (5 : ℝ) ^ (1 / (k : ℝ)) * t := by
    rw [Real.mul_rpow (by norm_num) (by positivity), hroot]
  have hscale := kolmogorov_bound_at_scale 3 μ ν B hB herror
    (t ^ k) (by positivity) (A * (5 * t ^ k) ^ (1 / (k : ℝ)))
    (hinterval (5 * t ^ k) (by positivity))
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, show (2 : ℝ) ^ 3 = 8 by norm_num] at hscale
  calc
    kolmogorovDistance μ ν ≤
        A * (5 * t ^ k) ^ (1 / (k : ℝ)) + (8 / (t ^ k) ^ 4) * B := hscale
    _ = _ := by
      rw [hwidth, ← pow_mul, Nat.mul_comm k 4]
      ring
)

end BooleanAnalysis.GaussianSpace.Invariance
