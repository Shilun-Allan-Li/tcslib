/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Anticoncentration.Remez
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Polynomial

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial small-ball bounds on uniform intervals

## Main definitions

No new definitions.

## Main results

* `uniform_smallBall_le_of_lintegral_sq_eq`: bounds the normalized
  Lebesgue volume of a polynomial sublevel set on a nondegenerate interval.

## References

* [CW01] A. Carbery and J. Wright, Distributional and Lq norm inequalities
  for polynomials over convex bodies in Rn, Mathematical Research Letters
  8 (2001), 233–248, §4.
-/

open MeasureTheory Set

namespace BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration

/-- A polynomial of degree at most `d ≥ 1`, whose square integral against
the uniform probability measure on `[a, b]` is one, has normalized
sublevel-set volume at most `4 * exp 2 * ε ^ (1 / d)` for every `ε > 0`.

This is the uniform-interval consequence of the Remez method in [CW01, §4].
The normalization and coarse explicit constant are the formulation used here.

**Proof sketch.** Let `m` be the Lebesgue volume of the sublevel set.
The case `m = 0` is immediate. Otherwise interval Remez bounds the
polynomial throughout `[a, b]` by
`ε * (4 * exp 2 * (b - a) / m) ^ d`.
Integrate its square and use that both the interval volume and the assumed
square integral equal the positive length `b - a`. After cancellation,
comparison of positive `2 * d`-th powers gives
`m / (b - a) ≤ 4 * exp 2 * ε ^ (1 / d)`. -/
theorem uniform_smallBall_le_of_lintegral_sq_eq
    (p : Polynomial ℝ) (d : ℕ) (hp : p.natDegree ≤ d) (hd : 1 ≤ d)
    (a b : ℝ) (hab : a < b)
    (hnorm :
      (∫⁻ x in Icc a b, ENNReal.ofReal ((p.eval x) ^ 2) ∂volume) =
        ENNReal.ofReal (b - a))
    (ε : ℝ) (hε : 0 < ε) :
    (volume {x : ℝ | x ∈ Icc a b ∧ |p.eval x| ≤ ε}).toReal /
        (b - a) ≤
      4 * Real.exp 2 * ε ^ (1 / (d : ℝ)) :=
  (by
  let E : Set ℝ := {x : ℝ | x ∈ Icc a b ∧ |p.eval x| ≤ ε}
  let m : ℝ := (volume E).toReal
  let A : ℝ := 4 * Real.exp 2 * (b - a)
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  change m / (b - a) ≤ _
  by_cases hm : 0 < m
  · let B : ℝ := ε * (A / m) ^ d
    have hBnonneg : 0 ≤ B := by dsimp only [B]; positivity
    have hbound (x : ℝ) (hx : x ∈ Icc a b) : |p.eval x| ≤ B :=
      abs_eval_le_of_bound_on_set p d hp E a b ε hab.le
        (fun y hy => hy.1) hm hε.le (fun y hy => hy.2) x hx
    have hle : ENNReal.ofReal (b - a) ≤
        ENNReal.ofReal (B ^ 2 * (b - a)) := by
      calc
        _ = ∫⁻ x in Icc a b, ENNReal.ofReal ((p.eval x) ^ 2) := hnorm.symm
        _ ≤ ∫⁻ x in Icc a b, ENNReal.ofReal (B ^ 2) := by
          apply setLIntegral_mono' measurableSet_Icc
          intro x hx
          exact ENNReal.ofReal_le_ofReal (by
            simpa only [sq_abs] using
              pow_le_pow_left₀ (abs_nonneg (p.eval x)) (hbound x hx) 2)
        _ = _ := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
            ← ENNReal.ofReal_mul (sq_nonneg B)]
    have hreal : b - a ≤ B ^ 2 * (b - a) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
    have hB : 1 ≤ B := by
      have : 1 ≤ B ^ 2 := by nlinarith
      nlinarith
    have hmbound : m ≤ A * ε ^ (1 / (d : ℝ)) := by
      have hd0 : d ≠ 0 := by omega
      have hroot : (ε ^ (1 / (d : ℝ))) ^ d = ε := by
        rw [one_div, Real.rpow_inv_natCast_pow hε.le hd0]
      apply (pow_le_pow_iff_left₀ hm.le
        (by positivity : 0 ≤ A * ε ^ (1 / (d : ℝ))) hd0).mp
      rw [mul_pow, hroot]
      have h : 1 * m ^ d ≤ A ^ d * ε := (le_div_iff₀ (pow_pos hm d)).mp (by
        calc
          _ ≤ ε * (A / m) ^ d := hB
          _ = _ := by rw [div_pow]; ring)
      simpa only [one_mul] using h
    apply (div_le_iff₀ hlen).mpr
    calc
      _ ≤ A * ε ^ (1 / (d : ℝ)) := hmbound
      _ = _ := by dsimp only [A]; ring
  · exact (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hm) hlen.le).trans (by positivity)
)

end BooleanAnalysis.GaussianSpace.PolynomialAnticoncentration
