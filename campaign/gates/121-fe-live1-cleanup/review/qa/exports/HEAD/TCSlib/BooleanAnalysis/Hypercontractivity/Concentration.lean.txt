/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Scalar parameters for hypercontractive concentration

This module collects the real-variable inequalities used to optimize moment
bounds in concentration estimates on the Boolean cube and finite products.

## Main definitions

There are no new definitions.

## Main results

* `concentration_parameter`: the cube threshold makes the optimizing moment
  exponent at least two.
* `concentration_optimized_moment`: the optimized cube moment equals its
  exponential tail factor.
* `scaled_concentration_parameter` and `scaled_concentration_optimized_moment`:
  the corresponding scalar statements for a positive atom parameter.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014; May 2021 arXiv version. Chapters 9–10, Theorems 9.23 and 10.24.
-/

namespace BooleanAnalysis.Hypercontractivity.ConcentrationAux

/-- For positive `k`, the threshold `t ≥ (√(2e)) ^ k` implies `t > 0`
and makes the concentration parameter `t ^ (2 / k) / e` at least two.
[OD14, Thm. 9.23 (proof)]

**Proof sketch.** The threshold is positive, so `t` is positive.
Raise the threshold inequality to the positive power `2 / k`;
the lower bound becomes `2e`. Divide by the positive number `e`. -/
lemma concentration_parameter {k : ℕ} (hk : 0 < k) (t : ℝ)
    (ht : Real.sqrt (2 * Real.exp 1) ^ k ≤ t) :
    0 < t ∧ 2 ≤ t ^ (2 / (k : ℝ)) / Real.exp 1 :=
  (by
  have hs : 0 < Real.sqrt (2 * Real.exp 1) :=
    Real.sqrt_pos.mpr (by positivity)
  have ht0 : 0 < t := lt_of_lt_of_le (pow_pos hs k) ht
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  refine ⟨ht0, ?_⟩
  have hpow := Real.rpow_le_rpow (pow_pos hs k).le ht
    (by positivity : 0 ≤ 2 / (k : ℝ))
  rw [← Real.rpow_natCast _ k, ← Real.rpow_mul hs.le,
    mul_div_cancel₀ 2 hkR.ne', Real.rpow_two, Real.sq_sqrt (by positivity)] at hpow
  exact (le_div_iff₀ (Real.exp_pos 1)).mpr hpow
)

/-- For positive degree `k` and threshold `t`, the optimizing moment exponent
`q = t ^ (2 / k) / e` gives
`((√q) ^ k / t) ^ q = exp(-k t ^ (2 / k) / (2e))`.
[OD14, Thm. 9.23 (proof)]

**Proof sketch.** The exponent `q` is positive and satisfies
`log q = (2 / k) log t - 1`. Thus the logarithm of `(√q) ^ k / t`
is `-k / 2`. Express the real power through the exponential, substitute
the chosen value of `q`, and simplify. -/
lemma concentration_optimized_moment {k : ℕ} (hk : 0 < k)
    (t : ℝ) (ht : 0 < t) :
    let q : ℝ := t ^ (2 / (k : ℝ)) / Real.exp 1
    (Real.sqrt q ^ k / t) ^ q =
      Real.exp (-(k : ℝ) / (2 * Real.exp 1) * t ^ (2 / (k : ℝ))) :=
  (by
  let q : ℝ := t ^ (2 / (k : ℝ)) / Real.exp 1
  change (Real.sqrt q ^ k / t) ^ q =
    Real.exp (-(k : ℝ) / (2 * Real.exp 1) * t ^ (2 / (k : ℝ)))
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hq : 0 < q := div_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)
  have hlogq : Real.log q = (2 / (k : ℝ)) * Real.log t - 1 := by
    dsimp [q]
    rw [Real.log_div (Real.rpow_pos_of_pos ht _).ne' (Real.exp_pos _).ne',
      Real.log_rpow ht, Real.log_exp]
  have hratio : Real.log (Real.sqrt q ^ k / t) = -(k : ℝ) / 2 := by
    rw [Real.log_div (pow_pos (Real.sqrt_pos.mpr hq) k).ne' ht.ne',
      Real.log_pow, Real.log_sqrt hq.le, hlogq]
    field_simp [hkR.ne']
    ring
  rw [Real.rpow_def_of_pos (div_pos (pow_pos (Real.sqrt_pos.mpr hq) k) ht),
    hratio]
  congr 1
  dsimp [q]
  field_simp
)


/-- Multiplying a positive threshold by `(√lam) ^ k` multiplies its
`2 / k` power by `lam`, for positive degree `k` and atom parameter `lam`.
[OD14, Thm. 10.24 (proof)]

**Proof sketch.** Distribute the real power over the positive factors,
rewrite the natural power as a real power, and combine the exponents.
Since `k * (2 / k) = 2`, the square-root factor becomes `lam`. -/
private lemma scaled_threshold_rpow {k : ℕ} (hk : 0 < k)
    (lam : ℝ) (hlam : 0 < lam) (t : ℝ) (ht : 0 < t) :
    (t * Real.sqrt lam ^ k) ^ (2 / (k : ℝ)) =
      lam * t ^ (2 / (k : ℝ)) :=
  (by
  rw [Real.mul_rpow ht.le (pow_nonneg (Real.sqrt_nonneg lam) k),
    ← Real.rpow_natCast _ k, ← Real.rpow_mul (Real.sqrt_nonneg lam),
    mul_div_cancel₀ 2 (Nat.cast_pos.mpr hk).ne', Real.rpow_two,
    Real.sq_sqrt hlam.le, mul_comm]
)


/-- For positive degree `k` and atom parameter `lam`, the threshold
`t ≥ (√(2e / lam)) ^ k` is positive and makes the optimizing exponent
`lam * t ^ (2 / k) / e` at least two. [OD14, Thm. 10.24 (proof)]

**Proof sketch.** Set `s = t * (√lam) ^ k`. Scaling the threshold gives
`s ≥ (√(2e)) ^ k`. Apply `concentration_parameter` to `s` and use
`s ^ (2 / k) = lam * t ^ (2 / k)`. -/
lemma scaled_concentration_parameter {k : ℕ} (hk : 0 < k)
    (lam : ℝ) (hlam : 0 < lam) (t : ℝ)
    (ht : Real.sqrt (2 * Real.exp 1 / lam) ^ k ≤ t) :
    0 < t ∧ 2 ≤ lam * t ^ (2 / (k : ℝ)) / Real.exp 1 :=
  (by
  have ht0 : 0 < t :=
    lt_of_lt_of_le (by positivity : 0 < Real.sqrt (2 * Real.exp 1 / lam) ^ k) ht
  have hthreshold : Real.sqrt (2 * Real.exp 1) ^ k ≤ t * Real.sqrt lam ^ k := calc
    Real.sqrt (2 * Real.exp 1) ^ k =
        Real.sqrt (2 * Real.exp 1 / lam) ^ k * Real.sqrt lam ^ k := by
      rw [← mul_pow, ← Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.exp 1 / lam),
        div_mul_cancel₀ _ hlam.ne']
    _ ≤ t * Real.sqrt lam ^ k :=
      mul_le_mul_of_nonneg_right ht (pow_nonneg (Real.sqrt_nonneg lam) k)
  obtain ⟨_, hq⟩ := concentration_parameter hk (t * Real.sqrt lam ^ k) hthreshold
  rw [scaled_threshold_rpow hk lam hlam t ht0] at hq
  exact ⟨ht0, hq⟩
)


/-- For positive degree, atom parameter, and threshold, the optimizing
moment exponent gives the product concentration factor.
[OD14, Thm. 10.24 (proof)]

**Proof sketch.** Set `s = t * (√lam) ^ k`, so the optimizing exponent
equals `s ^ (2 / k) / e`. Factor the real power on the left as `lam ^ k`
times the cube optimized moment at `s`, apply
`concentration_optimized_moment`, and substitute
`s ^ (2 / k) = lam * t ^ (2 / k)`. -/
lemma scaled_concentration_optimized_moment {k : ℕ} (hk : 0 < k)
    (lam : ℝ) (hlam : 0 < lam) (t : ℝ) (ht : 0 < t) :
    let q : ℝ := lam * t ^ (2 / (k : ℝ)) / Real.exp 1
    ((Real.sqrt q * lam ^ (1 / q - 1 / 2)) ^ k / t) ^ q =
      lam ^ k *
        Real.exp (-(k : ℝ) / (2 * Real.exp 1) * lam * t ^ (2 / (k : ℝ))) :=
  (by
  let q : ℝ := lam * t ^ (2 / (k : ℝ)) / Real.exp 1
  let s : ℝ := t * Real.sqrt lam ^ k
  change ((Real.sqrt q * lam ^ (1 / q - 1 / 2)) ^ k / t) ^ q =
    lam ^ k *
      Real.exp (-(k : ℝ) / (2 * Real.exp 1) * lam * t ^ (2 / (k : ℝ)))
  have hq : 0 < q :=
    div_pos (mul_pos hlam (Real.rpow_pos_of_pos ht _)) (Real.exp_pos _)
  have hs : 0 < s := mul_pos ht (pow_pos (Real.sqrt_pos.mpr hlam) k)
  have hscale : s ^ (2 / (k : ℝ)) = lam * t ^ (2 / (k : ℝ)) :=
    scaled_threshold_rpow hk lam hlam t ht
  have hmoment := concentration_optimized_moment hk s hs
  change (Real.sqrt (s ^ (2 / (k : ℝ)) / Real.exp 1) ^ k / s) ^
      (s ^ (2 / (k : ℝ)) / Real.exp 1) =
    Real.exp (-(k : ℝ) / (2 * Real.exp 1) * s ^ (2 / (k : ℝ))) at hmoment
  rw [hscale, ← mul_assoc] at hmoment
  have hfactor :
      (Real.sqrt q * lam ^ (1 / q - 1 / 2)) ^ k / t =
        (lam ^ (1 / q)) ^ k * (Real.sqrt q ^ k / s) := by
    dsimp only [s]
    rw [Real.rpow_sub hlam, ← Real.sqrt_eq_rpow, mul_pow, div_pow]
    field_simp [ht.ne', (pow_pos (Real.sqrt_pos.mpr hlam) k).ne']
  rw [hfactor,
    Real.mul_rpow (by positivity : 0 ≤ (lam ^ (1 / q)) ^ k)
      (by positivity : 0 ≤ Real.sqrt q ^ k / s),
    Real.rpow_pow_comm hlam.le, ← Real.rpow_mul (pow_nonneg hlam.le k),
    one_div_mul_cancel hq.ne', Real.rpow_one, hmoment]
)



end BooleanAnalysis.Hypercontractivity.ConcentrationAux
