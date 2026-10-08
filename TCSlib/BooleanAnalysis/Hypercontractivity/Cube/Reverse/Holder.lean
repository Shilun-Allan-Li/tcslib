/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.Reverse.Tensorization

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reverse Hölder inequality

One stage of Borell's reverse Bonami–Beckner argument, retaining the extended-mean conventions.

## Main definitions

Shared definitions are imported; local technical helpers accompany their proofs.

## Main results

* `ReverseMoments.expect_rpow_pos`.
* `ReverseMoments.expect_normalized_rpow_eq_one`.
* `reverse_holder`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014, Exercises 10.6–10.9.
-/

open BooleanAnalysis MeasureTheory Set Filter ProbabilityTheory Real
open scoped BigOperators ENNReal Classical

namespace BooleanAnalysis.Hypercontractivity

variable {n : ℕ}

attribute [local simp] BooleanAnalysis.Hypercontractivity.cubeLpNorm

/-- The reverse Young inequality: for `0 < r < 1` and conjugate exponent
`r / (r - 1) < 0` the arithmetic-geometric comparison reverses.

**Proof sketch.** Normalize a by b^(1/(r − 1)) and apply the concave tangent-line bound for t^r
at one. Multiply by the positive factor b^(r/(r − 1)) and rearrange.
-/
private lemma reverse_young {r a b : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ha : 0 ≤ a) (hb : 0 < b) :
    a * b ≥ a ^ r / r + b ^ (r / (r - 1)) / (r / (r - 1)) := by
  have hrm1 : r - 1 ≠ 0 := (sub_neg.mpr hr1).ne
  have hbase : 0 < b ^ (1 / (r - 1)) := Real.rpow_pos_of_pos hb _
  set t : ℝ := a / b ^ (1 / (r - 1)) with ht_def
  have ht : 0 ≤ t := div_nonneg ha hbase.le
  have haeq : a = t * b ^ (1 / (r - 1)) := by rw [ht_def]; field_simp
  -- the tangent line inequality at `t = 1` for the concave power `t ^ r`
  have htan : t ^ r ≤ 1 + r * (t - 1) := by
    simpa using rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hr0.le hr1.le
  have haq : a ^ r = t ^ r * b ^ (r / (r - 1)) := by
    rw [haeq, Real.mul_rpow ht hbase.le, ← Real.rpow_mul hb.le]
    congr 2
    ring
  have habeq : a * b = t * b ^ (r / (r - 1)) := by
    calc
      a * b = t * (b ^ (1 / (r - 1)) * b ^ (1 : ℝ)) := by rw [haeq, Real.rpow_one]; ring
      _ = t * b ^ (1 / (r - 1) + 1) := by rw [Real.rpow_add hb]
      _ = t * b ^ (r / (r - 1)) := by
        congr 2
        field_simp
        ring
  rw [haq, habeq]
  field_simp [hr0.ne', hrm1]
  nlinarith [mul_le_mul_of_nonneg_right htan (Real.rpow_nonneg hb.le (r / (r - 1)))]

/-- A nonnegative function with a positive value has positive `r`-th moment. -/
lemma ReverseMoments.expect_rpow_pos {r : ℝ} {u : BooleanFunc n} (hu : ∀ x, 0 ≤ u x)
    (hex : ∃ x, 0 < u x) : 0 < expect (fun x ↦ u x ^ r) := by
  obtain ⟨x, hx⟩ := hex
  unfold expect uniformWeight
  exact mul_pos (pow_pos (by norm_num) _)
    (Finset.sum_pos' (fun z _ ↦ Real.rpow_nonneg (hu z) _)
      ⟨x, Finset.mem_univ x, Real.rpow_pos_of_pos hx _⟩)

/-- Dividing by its own `L^r` mean normalizes the `r`-th moment to `1`. -/
lemma ReverseMoments.expect_normalized_rpow_eq_one {r : ℝ} (hr0 : r ≠ 0) (u : BooleanFunc n)
    (hu : ∀ x, 0 ≤ u x) (hE : 0 < expect (fun x ↦ u x ^ r)) :
    expect (fun x ↦ (u x / (expect (fun z ↦ u z ^ r)) ^ (1 / r)) ^ r) = 1 := by
  set E := expect (fun z ↦ u z ^ r)
  have hpow : (E ^ (1 / r)) ^ r = E := by
    rw [← Real.rpow_mul hE.le, one_div_mul_cancel hr0, Real.rpow_one]
  simp_rw [Real.div_rpow (hu _) (Real.rpow_pos_of_pos hE _).le, hpow]
  unfold expect
  rw [← Finset.sum_div, ← mul_div_assoc]
  exact div_self hE.ne'

/-- Rescaling both arguments of the inner product. -/
private lemma innerProduct_eq_mul_expect_div (u v : BooleanFunc n) {A B : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    innerProduct u v = A * B * expect (fun x ↦ (u x / A) * (v x / B)) := by
  have hx (x : BoolCube n) : u x * v x = A * B * ((u x / A) * (v x / B)) := by field_simp
  unfold innerProduct expect
  simp_rw [hx, ← Finset.mul_sum]
  ring

/-- Reverse Hölder for a positive exponent `r < 1` and its negative conjugate.

**Proof sketch.** If u is identically zero or v has a zero, the product of means vanishes.
Otherwise normalize both functions by their positive means, making both conjugate moments one.
Average reverse Young, use 1/r + 1/s = 1, and rescale.
-/
private lemma reverse_holder_of_pos (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (u v : BooleanFunc n) (hu : IsNonnegative u) (hv : IsNonnegative v) :
    innerProduct u v ≥ lpMean r u * lpMean (r / (r - 1)) v := by
  classical
  set s := r / (r - 1) with hs_def
  have hsneg : s < 0 := div_neg_of_pos_of_neg hr0 (sub_neg.mpr hr1)
  by_cases hupos : ∃ x, 0 < u x
  · by_cases hvzero : ∃ x, v x = 0
    · -- a zero of `v` makes the right-hand side vanish
      rw [show lpMean s v = 0 by simp [lpMean, hvzero, hsneg.le], mul_zero]
      unfold innerProduct
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ mul_nonneg (hu x) (hv x)
    · have hvpos (x : BoolCube n) : 0 < v x :=
        (hv x).lt_of_ne (Ne.symm (not_exists.mp hvzero x))
      have hEu : 0 < expect (fun x ↦ u x ^ r) := ReverseMoments.expect_rpow_pos hu hupos
      have hEv : 0 < expect (fun x ↦ v x ^ s) :=
        ReverseMoments.expect_rpow_pos hv ⟨Classical.arbitrary _, hvpos _⟩
      set A := (expect (fun x ↦ u x ^ r)) ^ (1 / r) with hA_def
      set B := (expect (fun x ↦ v x ^ s)) ^ (1 / s) with hB_def
      have hApos : 0 < A := Real.rpow_pos_of_pos hEu _
      have hBpos : 0 < B := Real.rpow_pos_of_pos hEv _
      -- the pointwise reverse Young inequality, averaged over the cube
      have hone : 1 ≤ expect (fun x ↦ (u x / A) * (v x / B)) := by
        have hright : expect (fun x ↦ (u x / A) ^ r / r + (v x / B) ^ s / s) = 1 := by
          have hnormu := ReverseMoments.expect_normalized_rpow_eq_one hr0.ne' u hu hEu
          have hnormv := ReverseMoments.expect_normalized_rpow_eq_one hsneg.ne v hv hEv
          rw [← hA_def] at hnormu
          rw [← hB_def] at hnormv
          unfold expect at hnormu hnormv ⊢
          rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, mul_add,
            ← mul_div_assoc, ← mul_div_assoc, hnormu, hnormv, hs_def]
          field_simp
          ring
        rw [← hright]
        unfold expect
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun x _ ↦ reverse_young hr0 hr1
            (div_nonneg (hu x) hApos.le) (div_pos (hvpos x) hBpos))
          (pow_nonneg (by norm_num) _)
      have hpu : lpMean r u = A := by
        rw [lpMean_of_pos r hr0, hA_def]
        simp_rw [abs_of_nonneg (hu _)]
      have hsv : lpMean s v = B := by
        rw [hB_def]
        simp [lpMean, hvzero, hsneg.ne, abs_of_pos (hvpos _)]
      rw [hpu, hsv, innerProduct_eq_mul_expect_div u v hApos.ne' hBpos.ne']
      nlinarith [mul_le_mul_of_nonneg_left hone (mul_nonneg hApos.le hBpos.le)]
  · -- `u` vanishes identically
    obtain rfl : u = 0 := funext fun x ↦ le_antisymm (not_lt.mp (not_exists.mp hupos x)) (hu x)
    simp [innerProduct, lpMean, expect, uniformWeight, hr0.ne', not_le.mpr hr0]

/-- Reverse Hölder bounds the inner product below by the product of conjugate means
for finite `p < 1`, `p ≠ 0`. This is the inequality consequence of the source's sharp
infimum-duality identity, used in the two-function corollary; the full identity and
its infinite-exponent endpoint are not asserted here.

**Source:** [OD14, Exs. 10.6--10.9]. -/
lemma reverse_holder (p : ℝ) (hp : p < 1) (hp0 : p ≠ 0)
    (f g : BooleanFunc n) (hf : IsNonnegative f) (hg : IsNonnegative g) :
    innerProduct f g ≥ lpMean p f * lpMean (p / (p - 1)) g := by
  rcases lt_or_gt_of_ne hp0 with hpneg | hppos
  · -- for `p < 0` apply the positive case to the conjugate exponent
    have hpm1 : p - 1 ≠ 0 := (sub_neg.mpr hp).ne
    have hq0 : 0 < p / (p - 1) := div_pos_of_neg_of_neg hpneg (sub_neg.mpr hp)
    have hq1 : p / (p - 1) < 1 := by
      rw [div_lt_iff_of_neg (sub_neg.mpr hp)]
      linarith
    have hconj : (p / (p - 1)) / (p / (p - 1) - 1) = p := by field_simp; ring
    have h := reverse_holder_of_pos (p / (p - 1)) hq0 hq1 g f hg hf
    rw [hconj] at h
    simpa only [BooleanAnalysis.innerProduct_comm, mul_comm] using h
  · exact reverse_holder_of_pos p hppos hp f g hf hg

end BooleanAnalysis.Hypercontractivity
