/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Reverse.Basic
import Mathlib.Analysis.Analytic.Binomial

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reverse two-point inequality

One stage of Borell's reverse Bonami–Beckner argument, retaining the extended-mean conventions.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `borell_factor_bound`.
* `reverse_two_point_normalized`.
* `normalize_one_bit`.
* `reverse_bonami_beckner_one_bit`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Exercises 10.6–10.9.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

attribute [local simp] BooleanAnalysis.Hypercontractivity.cubeLpNorm

/-! ### The two-point inequality -/

/-- Newton's binomial series: for `|x| < 1` the function `(1 + x) ^ s` is the sum
of the generalized binomial series. -/
private lemma hasSum_choose_rpow {s x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ ↦ Ring.choose s k * x ^ k) ((1 + x) ^ s) := by
  have hsum := (one_add_rpow_hasFPowerSeriesOnBall_zero (a := s)).hasSum_sub
    (show x ∈ EMetric.ball (0 : ℝ) 1 by
      simpa [EMetric.mem_ball, edist_dist, Real.dist_eq] using hx)
  convert hsum using 1
  ext k
  simp [binomialSeries, mul_comm]

/-- The even part of the binomial series is summable. -/
private lemma summable_choose_even {s x : ℝ} (hx : |x| < 1) :
    Summable (fun k : ℕ ↦ Ring.choose s (2 * k) * x ^ (2 * k)) :=
  (hasSum_choose_rpow hx).summable.comp_injective
    (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))

/-- Symmetrizing the binomial series kills the odd terms.

**Proof sketch.** Average the generalized binomial series at x and −x. Odd terms cancel and even
terms agree, leaving the series indexed by even powers.
-/
private lemma even_part_rpow_eq_tsum {s x : ℝ} (hx : |x| < 1) :
    ((1 + x) ^ s + (1 - x) ^ s) / 2 =
      ∑' k : ℕ, Ring.choose s (2 * k) * x ^ (2 * k) := by
  have hxneg : |-x| < 1 := by simpa using hx
  have hboth : HasSum
      (fun k : ℕ ↦ (Ring.choose s k * x ^ k + Ring.choose s k * (-x) ^ k) / 2)
      (((1 + x) ^ s + (1 + -x) ^ s) / 2) :=
    ((hasSum_choose_rpow hx).add (hasSum_choose_rpow hxneg)).div_const 2
  have heven := (summable_choose_even (s := s) hx).hasSum
  have hall : HasSum
      (fun k : ℕ ↦ (Ring.choose s k * x ^ k + Ring.choose s k * (-x) ^ k) / 2)
      ((∑' k : ℕ, Ring.choose s (2 * k) * x ^ (2 * k)) + 0) := by
    apply HasSum.even_add_odd
    · convert heven using 1
      funext k
      rw [Even.neg_pow (even_two.mul_right k)]
      ring
    · convert (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0) using 1
      funext k
      rw [show (-x) ^ (2 * k + 1) = -(x ^ (2 * k + 1)) by
        rw [pow_add, Even.neg_pow (even_two.mul_right k), pow_one]
        ring]
      ring
  rw [show 1 - x = 1 + -x by ring]
  simpa using hboth.unique hall

/-- The `L^s` moment of the one-bit function `1 + b χ`, for `|b| < 1`. -/
private lemma expect_abs_rpow_affine (s b : ℝ) (hb : |b| < 1) :
    expect (fun x : BoolCube 1 ↦ |1 + b * boolToSign (x 0)| ^ s) =
      ((1 + b) ^ s + (1 - b) ^ s) / 2 := by
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
  set f : BooleanFunc 1 := fun x ↦ 1 + b * boolToSign (x 0) with hf_def
  have hfalse : (1 : ℝ) + b = fourierCoeff f ∅ + fourierCoeff f {⟨0, by omega⟩} := by
    rw [← one_bit_val_false f, hf_def]
    norm_num [boolToSign]
  have htrue : (1 : ℝ) - b = fourierCoeff f ∅ - fourierCoeff f {⟨0, by omega⟩} := by
    rw [← one_bit_val_true f, hf_def]
    norm_num [boolToSign]
    ring
  rw [expect_abs_rpow_one_bit, show fourierCoeff f ∅ = 1 by linarith,
    show fourierCoeff f {⟨0, by omega⟩} = b by linarith,
    abs_of_pos (by linarith : (0:ℝ) < 1 + b), abs_of_pos (by linarith : (0:ℝ) < 1 - b)]

/-- The second generalized binomial coefficient. -/
private lemma ring_choose_two (s : ℝ) : Ring.choose s 2 = s * (s - 1) / 2 := by
  have h := Ring.choose_smul_choose (R := ℝ) s (show 1 ≤ 2 by omega)
  norm_num [nsmul_eq_mul, Ring.choose_one_right] at h ⊢
  linarith

/-- Two steps of Pascal's recurrence for generalized binomial coefficients. -/
private lemma ring_choose_even_succ (s : ℝ) (k : ℕ) :
    Ring.choose s (2 * (k + 1)) =
      Ring.choose s (2 * k) * (s - (2 * k : ℕ)) * (s - (2 * k + 1 : ℕ)) /
        (((2 * k + 1 : ℕ) : ℝ) * ((2 * k + 2 : ℕ) : ℝ)) := by
  have h1 := Ring.choose_smul_choose (R := ℝ) s (Nat.le_succ (2 * k))
  have h2 := Ring.choose_smul_choose (R := ℝ) s (Nat.le_succ (2 * k + 1))
  simp only [nsmul_eq_mul] at h1 h2
  norm_num at h1 h2 ⊢
  have h1' : Ring.choose s (2 * k + 1) =
      Ring.choose s (2 * k) * (s - 2 * (k : ℝ)) / (2 * (k : ℝ) + 1) :=
    (eq_div_iff (by positivity)).2 (by nlinarith [h1])
  have h2' : Ring.choose s (2 * k + 1 + 1) =
      Ring.choose s (2 * k + 1) * (s - (2 * (k : ℝ) + 1)) / (2 * (k : ℝ) + 2) :=
    (eq_div_iff (by positivity)).2 (by nlinarith [h2])
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, h2', h1']
  field_simp

/-- For an exponent in `(0, 1)` all even generalized binomial coefficients past
the constant term are nonpositive. -/
private lemma ring_choose_even_nonpos (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ k : ℕ, 1 ≤ k → Ring.choose s (2 * k) ≤ 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      match k, hk with
      | 1, _ =>
          rw [ring_choose_two]
          nlinarith
      | (k + 2), _ =>
          rw [ring_choose_even_succ]
          have hprev := ih (k + 1) (by omega) (by omega)
          have hfac : 0 ≤ (s - (2 * (k + 1) : ℕ)) * (s - (2 * (k + 1) + 1 : ℕ)) := by
            apply mul_nonneg_of_nonpos_of_nonpos <;> norm_num <;> linarith
          refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
          rw [mul_assoc]
          exact mul_nonpos_of_nonpos_of_nonneg hprev hfac

/-- The scalar factor estimate used to compare corresponding even Taylor
coefficients in Borell's proof. -/
lemma borell_factor_bound (p q ρ : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p < 1)
    (hρ0 : 0 ≤ ρ) (hρsq : ρ ^ 2 = (1 - p) / (1 - q))
    (m : ℕ) (hm : 2 ≤ m) :
    ρ * ((m : ℝ) - q) ≤ (m : ℝ) - p := by
  have hq1 : q < 1 := hqp.trans hp
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hρrel : ρ ^ 2 * (1 - q) = 1 - p := by
    rw [hρsq, div_mul_cancel₀ _ (sub_pos.mpr hq1).ne']
  have hquad : 0 ≤ (m : ℝ) ^ 2 - 2 * m + p + q - p * q := by
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) by linarith) (show 0 ≤ (m : ℝ) - 2 by linarith),
      mul_nonneg hq.le (sub_pos.mpr hp).le]
  refine (sq_le_sq₀ (mul_nonneg hρ0 (by linarith)) (by linarith)).mp ?_
  have key : 0 ≤ ((m : ℝ) - p) ^ 2 * (1 - q) - ρ ^ 2 * (1 - q) * ((m : ℝ) - q) ^ 2 := by
    rw [hρrel]
    nlinarith [mul_nonneg (sub_nonneg.mpr hqp.le) hquad]
  nlinarith [key, sub_pos.mpr hq1]

/-- The inductive step of the coefficient comparison: Pascal's recurrence turns
the bound for `2K` into the bound for `2K + 2`, at the cost of the two factors
controlled by `borell_factor_bound`.

**Proof sketch.** Apply two binomial recurrences to express the next even coefficients using the
preceding ones and two new factors. Borell's scalar bound compares those factors after
multiplication by ρ²; the nonpositive comparison coefficient reverses the inequality. Use the
preceding coefficient bound and divide by the positive common denominator.
-/
private lemma choose_even_ratio_step (p q ρ : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p < 1)
    (hρ0 : 0 ≤ ρ) (hρsq : ρ ^ 2 = (1 - p) / (1 - q)) (K : ℕ) (hK : 1 ≤ K)
    (hih : Ring.choose p (2 * K) ≤ (p / q) * Ring.choose q (2 * K) * ρ ^ (2 * K)) :
    Ring.choose p (2 * (K + 1)) ≤
      (p / q) * Ring.choose q (2 * (K + 1)) * ρ ^ (2 * (K + 1)) := by
  have hp0 : 0 < p := hq.trans hqp
  have hq1 : q < 1 := hqp.trans hp
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hm1 : 0 ≤ ((2 * K + 1 : ℕ) : ℝ) - q := by push_cast; linarith
  have hmp0 : 0 ≤ ((2 * K : ℕ) : ℝ) - p := by push_cast; linarith
  have hmp1 : 0 ≤ ((2 * K + 1 : ℕ) : ℝ) - p := by push_cast; linarith
  -- the two factors introduced by Pascal's recurrence shrink by at least `ρ ^ 2`
  have hfac : ρ ^ 2 * ((((2 * K : ℕ) : ℝ) - q) * (((2 * K + 1 : ℕ) : ℝ) - q)) ≤
      (((2 * K : ℕ) : ℝ) - p) * (((2 * K + 1 : ℕ) : ℝ) - p) := by
    calc
      ρ ^ 2 * ((((2 * K : ℕ) : ℝ) - q) * (((2 * K + 1 : ℕ) : ℝ) - q)) =
          (ρ * (((2 * K : ℕ) : ℝ) - q)) * (ρ * (((2 * K + 1 : ℕ) : ℝ) - q)) := by ring
      _ ≤ (((2 * K : ℕ) : ℝ) - p) * (((2 * K + 1 : ℕ) : ℝ) - p) :=
        mul_le_mul (borell_factor_bound p q ρ hq hqp hp hρ0 hρsq (2 * K) (by omega))
          (borell_factor_bound p q ρ hq hqp hp hρ0 hρsq (2 * K + 1) (by omega))
          (mul_nonneg hρ0 hm1) hmp0
  -- the comparison term is nonpositive, so multiplying by it reverses `hfac`
  have hrq_nonpos : (p / q) * Ring.choose q (2 * K) * ρ ^ (2 * K) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hp0.le hq.le)
        (ring_choose_even_nonpos q hq hq1 K hK))
      (pow_nonneg hρ0 _)
  have hnumle :
      Ring.choose p (2 * K) * (p - (2 * K : ℕ)) * (p - (2 * K + 1 : ℕ)) ≤
        (p / q) * (Ring.choose q (2 * K) * (q - (2 * K : ℕ)) *
          (q - (2 * K + 1 : ℕ))) * ρ ^ (2 * (K + 1)) := by
    calc
      Ring.choose p (2 * K) * (p - (2 * K : ℕ)) * (p - (2 * K + 1 : ℕ)) =
          Ring.choose p (2 * K) *
            ((((2 * K : ℕ) : ℝ) - p) * (((2 * K + 1 : ℕ) : ℝ) - p)) := by ring
      _ ≤ ((p / q) * Ring.choose q (2 * K) * ρ ^ (2 * K)) *
          ((((2 * K : ℕ) : ℝ) - p) * (((2 * K + 1 : ℕ) : ℝ) - p)) :=
        mul_le_mul_of_nonneg_right hih (mul_nonneg hmp0 hmp1)
      _ ≤ ((p / q) * Ring.choose q (2 * K) * ρ ^ (2 * K)) *
          (ρ ^ 2 * ((((2 * K : ℕ) : ℝ) - q) * (((2 * K + 1 : ℕ) : ℝ) - q))) :=
        mul_le_mul_of_nonpos_left hfac hrq_nonpos
      _ = (p / q) * (Ring.choose q (2 * K) * (q - (2 * K : ℕ)) *
          (q - (2 * K + 1 : ℕ))) * ρ ^ (2 * (K + 1)) := by
        rw [show 2 * (K + 1) = 2 * K + 2 by omega, pow_add]
        ring
  rw [ring_choose_even_succ p K, ring_choose_even_succ q K]
  convert div_le_div_of_nonneg_right hnumle
    (by positivity : (0:ℝ) ≤ (((2 * K + 1 : ℕ) : ℝ) * ((2 * K + 2 : ℕ) : ℝ))) using 1
  ring

/-- Coefficientwise comparison of the two even Taylor series in Borell's proof. -/
private lemma choose_even_ratio_le (p q ρ : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p < 1)
    (hρ0 : 0 ≤ ρ) (hρsq : ρ ^ 2 = (1 - p) / (1 - q)) :
    ∀ k : ℕ, 1 ≤ k →
      Ring.choose p (2 * k) ≤ (p / q) * Ring.choose q (2 * k) * ρ ^ (2 * k) := by
  have hq1 : q < 1 := hqp.trans hp
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
      match k with
      | 0 =>
          rw [ring_choose_two, ring_choose_two]
          field_simp [hq.ne', (sub_pos.mpr hq1).ne'] at hρsq ⊢
          norm_num [pow_two] at hρsq ⊢
          nlinarith
      | (k + 1) =>
          exact choose_even_ratio_step p q ρ hq hqp hp hρ0 hρsq (k + 1) (by omega)
            (ih (by omega))

/-- Lemma A.1 away from the endpoints `a = ±1`.  Expand both sides in even
powers of `a` and compare coefficients with `choose_even_ratio_le`.

**Proof sketch.** Expand the symmetric moments as convergent even binomial series and compare
their nonconstant terms coefficientwise. Writing the moments as P and Q gives P ≤ 1 + (p/q)(Q −
1), bounded by Q^(p/q) through the tangent-line inequality. Take the positive 1/p power.
-/
lemma reverse_two_point_normalized (p q ρ a : ℝ)
    (hq : 0 < q) (hqp : q < p) (hp : p < 1)
    (hρ0 : 0 ≤ ρ) (hρsq : ρ ^ 2 = (1 - p) / (1 - q))
    (ha : |a| < 1) :
    lpMean q (noiseOp ρ (fun x : BoolCube 1 ↦ 1 + a * boolToSign (x 0))) ≥
      lpMean p (fun x : BoolCube 1 ↦ 1 + a * boolToSign (x 0)) := by
  have hp0 : 0 < p := hq.trans hqp
  have hq1 : q < 1 := hqp.trans hp
  have hρ1 : ρ < 1 := by
    have : ρ ^ 2 < 1 := by rw [hρsq, div_lt_one (sub_pos.mpr hq1)]; linarith
    nlinarith [sq_nonneg ρ]
  have hρa : |ρ * a| < 1 := by
    rw [abs_mul, abs_of_nonneg hρ0]
    nlinarith [abs_nonneg a]
  -- the two Taylor series, with their constant terms split off
  have hsump := summable_choose_even (s := p) (x := a) ha
  have hsumq := summable_choose_even (s := q) (x := ρ * a) hρa
  have hPseries : ((1 + a) ^ p + (1 - a) ^ p) / 2 =
      1 + ∑' k : ℕ, Ring.choose p (2 * (k + 1)) * a ^ (2 * (k + 1)) := by
    rw [even_part_rpow_eq_tsum ha, hsump.tsum_eq_zero_add]
    simp
  have hQseries : ((1 + ρ * a) ^ q + (1 - ρ * a) ^ q) / 2 =
      1 + ∑' k : ℕ, Ring.choose q (2 * (k + 1)) * (ρ * a) ^ (2 * (k + 1)) := by
    rw [even_part_rpow_eq_tsum hρa, hsumq.tsum_eq_zero_add]
    simp
  -- comparison of the two tails
  have hterm (k : ℕ) :
      Ring.choose p (2 * (k + 1)) * a ^ (2 * (k + 1)) ≤
        (p / q) * (Ring.choose q (2 * (k + 1)) * (ρ * a) ^ (2 * (k + 1))) := by
    calc
      Ring.choose p (2 * (k + 1)) * a ^ (2 * (k + 1)) ≤
          ((p / q) * Ring.choose q (2 * (k + 1)) * ρ ^ (2 * (k + 1))) * a ^ (2 * (k + 1)) :=
        mul_le_mul_of_nonneg_right
          (choose_even_ratio_le p q ρ hq hqp hp hρ0 hρsq (k + 1) (by omega))
          (by rw [show 2 * (k + 1) = (k + 1) + (k + 1) by omega, pow_add]; exact mul_self_nonneg _)
      _ = (p / q) * (Ring.choose q (2 * (k + 1)) * (ρ * a) ^ (2 * (k + 1))) := by
        rw [mul_pow]; ring
  have htail :
      (∑' k : ℕ, Ring.choose p (2 * (k + 1)) * a ^ (2 * (k + 1))) ≤
        (p / q) * ∑' k : ℕ, Ring.choose q (2 * (k + 1)) * (ρ * a) ^ (2 * (k + 1)) := by
    rw [← tsum_mul_left]
    exact (hsump.comp_injective (add_left_injective 1)).tsum_le_tsum hterm
      ((hsumq.comp_injective (add_left_injective 1)).mul_left (p / q))
  -- the symmetrized moments are positive, and the tail comparison plus the
  -- tangent line inequality at `1` compares them
  obtain ⟨ha1, ha2⟩ := abs_lt.mp ha
  obtain ⟨hρa1, hρa2⟩ := abs_lt.mp hρa
  have hPpos : 0 < ((1 + a) ^ p + (1 - a) ^ p) / 2 := by
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 + a by linarith) p
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 - a by linarith) p
    linarith
  have hQpos : 0 < ((1 + ρ * a) ^ q + (1 - ρ * a) ^ q) / 2 := by
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 + ρ * a by linarith) q
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 - ρ * a by linarith) q
    linarith
  have hPQ : ((1 + a) ^ p + (1 - a) ^ p) / 2 ≤
      (((1 + ρ * a) ^ q + (1 - ρ * a) ^ q) / 2) ^ (p / q) := by
    calc
      ((1 + a) ^ p + (1 - a) ^ p) / 2 ≤
          1 + (p / q) * ((((1 + ρ * a) ^ q + (1 - ρ * a) ^ q) / 2) - 1) := by
        rw [hPseries, hQseries]; linarith
      _ ≤ (((1 + ρ * a) ^ q + (1 - ρ * a) ^ q) / 2) ^ (p / q) := by
        simpa using one_add_mul_self_le_rpow_one_add
          (s := (((1 + ρ * a) ^ q + (1 - ρ * a) ^ q) / 2) - 1) (by linarith)
          ((le_div_iff₀ hq).2 (by simpa using hqp.le))
  rw [ge_iff_le, lpMean_of_pos q hq, lpMean_of_pos p hp0, noiseOp_affine_one_bit,
    expect_abs_rpow_affine q (ρ * a) hρa, expect_abs_rpow_affine p a ha]
  refine (Real.rpow_le_rpow hPpos.le hPQ (by positivity)).trans_eq ?_
  rw [← Real.rpow_mul hQpos.le, show p / q * (1 / p) = 1 / q by field_simp]

/-- Every point of the one-bit cube is one of the two constant strings. -/
private lemma boolCube_one_cases (x : BoolCube 1) :
    x = (fun _ ↦ false) ∨ x = (fun _ ↦ true) := by
  cases hx : x 0
  · exact Or.inl (by funext i; fin_cases i; exact hx)
  · exact Or.inr (by funext i; fin_cases i; exact hx)

/-- A nonzero nonnegative one-bit function has the form `c (1 + a χ)` with
`c > 0` and `|a| ≤ 1`. -/
lemma normalize_one_bit (f : BooleanFunc 1) (hf : IsNonnegative f) (hf0 : f ≠ 0) :
    ∃ c a : ℝ, 0 < c ∧ -1 ≤ a ∧ a ≤ 1 ∧
      f = fun x ↦ c * (1 + a * boolToSign (x 0)) := by
  set u := f (fun _ ↦ false)
  set v := f (fun _ ↦ true)
  have hu : 0 ≤ u := hf _
  have hv : 0 ≤ v := hf _
  have huv : 0 < u + v := by
    rcases (by linarith : (0:ℝ) ≤ u + v).lt_or_eq with h | h
    · exact h
    · refine absurd (funext fun x ↦ ?_) hf0
      rcases boolCube_one_cases x with rfl | rfl
      · show u = 0; linarith
      · show v = 0; linarith
  refine ⟨(u + v) / 2, (u - v) / (u + v), by linarith, ?_, ?_, funext fun x ↦ ?_⟩
  · rw [le_div_iff₀ huv]; linarith
  · rw [div_le_iff₀ huv]; linarith
  · rcases boolCube_one_cases x with rfl | rfl <;>
      simp only [boolToSign_false, boolToSign_true] <;>
      field_simp <;> ring

/-- The one-bit power means depend continuously on the Fourier coefficient. -/
private lemma continuous_lpMean_affine (s : ℝ) (hs : 0 < s) :
    Continuous fun a : ℝ ↦ lpMean s (fun x : BoolCube 1 ↦ 1 + a * boolToSign (x 0)) := by
  simp_rw [lpMean_of_pos s hs]
  unfold expect
  refine (Real.continuous_rpow_const (by positivity)).comp
    (continuous_const.mul (continuous_finset_sum _ fun x _ ↦ ?_))
  exact (Real.continuous_rpow_const hs.le).comp
    (Continuous.abs (continuous_const.add (continuous_id.mul continuous_const)))

/-- The complete two-point reverse Bonami-Beckner inequality.  Homogeneity and
continuity discharge the zero function and the endpoints `a = ±1`.

**Source:** [OD14, Exs. 10.6--10.9].

**Proof sketch.** Handle the zero function directly. Every other nonnegative one-bit function is
a positive multiple of 1 + aχ with |a| ≤ 1. Apply the normalized estimate for |a| < 1, extend to
a = ±1 by continuity, and rescale.
-/
theorem reverse_bonami_beckner_one_bit (p q ρ : ℝ)
    (hq : 0 < q) (hqp : q < p) (hp : p < 1)
    (hρ0 : 0 ≤ ρ) (hρsq : ρ ^ 2 = (1 - p) / (1 - q))
    (f : BooleanFunc 1) (hf : IsNonnegative f) :
    lpMean q (noiseOp ρ f) ≥ lpMean p f := by
  have hp0 : 0 < p := hq.trans hqp
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [lpMean_of_pos p hp0, lpMean_of_pos q hq,
      show noiseOp ρ (0 : BooleanFunc 1) = 0 by
        funext x; simp [noiseOp, fourierCoeff, innerProduct, expect]]
    unfold expect
    simp only [Pi.zero_apply, abs_zero, Real.zero_rpow hp0.ne', Real.zero_rpow hq.ne',
      Finset.sum_const_zero, mul_zero, one_div]
    rw [Real.zero_rpow (inv_ne_zero hp0.ne'), Real.zero_rpow (inv_ne_zero hq.ne')]
  obtain ⟨c, a, hc, ha0, ha1, hfa⟩ := normalize_one_bit f hf hf0
  -- the inequality for `|a| < 1` extends to `a = ±1` by continuity
  have hclosed : IsClosed {b : ℝ |
      lpMean p (fun x : BoolCube 1 ↦ 1 + b * boolToSign (x 0)) ≤
        lpMean q (noiseOp ρ (fun x : BoolCube 1 ↦ 1 + b * boolToSign (x 0)))} :=
    isClosed_le (continuous_lpMean_affine p hp0)
      (by simpa only [noiseOp_affine_one_bit] using
        (continuous_lpMean_affine q hq).comp (continuous_const.mul continuous_id))
  have hIoo : Set.Ioo (-1 : ℝ) 1 ⊆ {b : ℝ |
      lpMean p (fun x : BoolCube 1 ↦ 1 + b * boolToSign (x 0)) ≤
        lpMean q (noiseOp ρ (fun x : BoolCube 1 ↦ 1 + b * boolToSign (x 0)))} := fun b hb ↦
    reverse_two_point_normalized p q ρ b hq hqp hp hρ0 hρsq (by rw [abs_lt]; exact hb)
  have hIcc := hclosed.closure_subset_iff.mpr hIoo
  rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] at hIcc
  rw [hfa, noiseOp_const_mul, lpMean_const_mul q c hq hc, lpMean_const_mul p c hp0 hc]
  exact mul_le_mul_of_nonneg_left (hIcc ⟨ha0, ha1⟩) hc.le

end BooleanAnalysis.Hypercontractivity
