/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import Mathlib.Analysis.Calculus.MeanValue
import TCSlib.BooleanAnalysis.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Linearization estimates for the Gaussian Bobkov limit

## Main definitions

No additional derivative representation is introduced. The estimates use an
explicit family of continuous linear maps witnessing the existing derivative.

## Main results

* A globally Lipschitz derivative gives a quadratic linearization remainder.
* Half increments approximate the corresponding half directional derivative,
  with an explicit quadratic error bound.

These bounds control the discrete derivatives of smooth functions evaluated on
normalized Boolean blocks. The constants are deliberately nonoptimal: the
quadratic remainder has constant C instead of C/2, which suffices for its
vanishing contribution as the block size tends to infinity.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, passage from Boolean to Gaussian Bobkov.
-/

open Set
open scoped BigOperators
open scoped NNReal

namespace BooleanAnalysis.GaussianSpace

/-- A function with a globally C-Lipschitz derivative has linearization error
at most C times the square of the displacement. [OD14, §11.4, Gaussian Bobkov limit]
The stated constant C is a convenient nonoptimal bound.

**Proof sketch.** Subtract the linear map given by the derivative at the base
point. On the ball with radius equal to the displacement, the new derivative
has norm at most C times that radius. The mean-value inequality gives the
quadratic remainder. -/
lemma norm_linearization_remainder_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (D x) x) {C : ℝ≥0} (hD : LipschitzWith C D)
    (x y : E) : ‖f y - f x - D x (y - x)‖ ≤ (C : ℝ) * ‖y - x‖ ^ 2 := by
  let g (z : E) := f z - D x z
  have hg (z : E) : HasFDerivAt g (D z - D x) z := (hf z).sub (D x).hasFDerivAt
  have h := (convex_closedBall x ‖y - x‖).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hg z).differentiableAt) (C := (C : ℝ) * ‖y - x‖)
    (fun z hz => by
      rw [(hg z).fderiv]
      exact (hD.norm_sub_le z x).trans (mul_le_mul_of_nonneg_left
        (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz) C.coe_nonneg))
    (show x ∈ Metric.closedBall x ‖y - x‖ by simp)
    (show y ∈ Metric.closedBall x ‖y - x‖ by simp [dist_eq_norm])
  convert h using 1
  · dsimp [g]
    rw [map_sub]
    congr 1
    ring
  · ring

/-- A half difference across an increment h times v differs from the half
linearized increment by at most (C/2) h² times the squared norm of v, when the
derivative is C-Lipschitz. [OD14, §11.4, Gaussian Bobkov limit]

**Proof sketch.** Apply the quadratic remainder to the increment h times v and
divide by two. Squaring its norm removes the sign of h, so the estimate holds
for every real increment. -/
lemma abs_half_increment_sub_derivative_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (D x) x) {C : ℝ≥0} (hD : LipschitzWith C D)
    (x v : E) (h : ℝ) :
    |(f (x + h • v) - f x) / 2 - (h / 2) * D x v| ≤
      (C : ℝ) / 2 * h ^ 2 * ‖v‖ ^ 2 := by
  have hrem := norm_linearization_remainder_le hf hD x (x + h • v)
  simp only [add_sub_cancel_left, map_smul, smul_eq_mul, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hrem
  calc
    _ = |f (x + h • v) - f x - h * D x v| / 2 := by
      rw [show (f (x + h • v) - f x) / 2 - (h / 2) * D x v =
        (f (x + h • v) - f x - h * D x v) / 2 by ring, abs_div]
      norm_num
    _ ≤ ((C : ℝ) * (h ^ 2 * ‖v‖ ^ 2)) / 2 := by
      exact div_le_div_of_nonneg_right hrem (by norm_num)
    _ = _ := by ring

/-- Updating one bit changes the normalized block vector by its signed
coordinate increment. [OD14, §11.1, BitsToGaussians]

**Proof sketch.** Only the updated block changes. In that block's sum, replace
the old sign by the new sign and divide by the common normalization. -/
lemma normalizedBoolBlocks_update {n m : ℕ}
    (x : Fin n → Fin m → Bool) (i : Fin n) (j : Fin m) (b : Bool) :
    (fun k : Fin n => (∑ l : Fin m,
      boolToSign (Function.update x i (Function.update (x i) j b) k l)) / Real.sqrt m) =
      (fun k : Fin n => (∑ l : Fin m, boolToSign (x k l)) / Real.sqrt m) +
        ((boolToSign b - boolToSign (x i j)) / Real.sqrt m) • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
  have hs : (∑ l : Fin m, boolToSign (Function.update (x i) j b l)) =
      (∑ l : Fin m, boolToSign (x i l)) + boolToSign b - boolToSign (x i j) := by
    change (∑ l : Fin m, (boolToSign ∘ Function.update (x i) j b) l) = _
    rw [Function.comp_update, Finset.sum_update_of_mem (Finset.mem_univ j)]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [Finset.sdiff_singleton_eq_erase, Function.comp_apply]
    ring
  ext k
  by_cases hk : k = i
  · subst k
    simp only [Function.update_self, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      smul_eq_mul, mul_one, hs]
    ring
  · simp [Function.update_of_ne hk, Pi.single_eq_of_ne hk]

/-- A discrete half difference of a smooth function on normalized Boolean
blocks approximates its corresponding partial derivative divided by the square
root of the block size, with error at most 2C divided by that size when the
derivative family is C-Lipschitz. [OD14, §11.4, Gaussian Bobkov limit]

**Proof sketch.** One endpoint equals the original block vector; the other
differs by plus or minus two over the square root of the block size in a unit
coordinate direction. Apply the half-increment quadratic remainder, splitting
on the old bit to orient the two endpoints. -/
lemma abs_normalizedBoolBlocks_half_difference_sub_derivative_le {n m : ℕ}
    {f : (Fin n → ℝ) → ℝ}
    {D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (D z) z) {C : ℝ≥0} (hD : LipschitzWith C D)
    (x : Fin n → Fin m → Bool) (i : Fin n) (j : Fin m) :
    |(f (fun k : Fin n => (∑ l : Fin m,
        boolToSign (Function.update x i (Function.update (x i) j false) k l)) /
          Real.sqrt m) -
      f (fun k : Fin n => (∑ l : Fin m,
        boolToSign (Function.update x i (Function.update (x i) j true) k l)) /
          Real.sqrt m)) / 2 -
      D (fun k : Fin n => (∑ l : Fin m, boolToSign (x k l)) / Real.sqrt m)
        (Pi.single i 1) / Real.sqrt m| ≤ 2 * (C : ℝ) / m := by
  let z : Fin n → ℝ := fun k => (∑ l : Fin m, boolToSign (x k l)) / Real.sqrt m
  let e : Fin n → ℝ := Pi.single i 1
  have hsq : (2 / Real.sqrt m) ^ 2 = 4 / (m : ℝ) := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    norm_num
  have hbound (a : ℝ) (ha : a ^ 2 = 4 / (m : ℝ)) :
      |(f (z + a • e) - f z) / 2 - (a / 2) * D z e| ≤ 2 * (C : ℝ) / m := by
    have h := abs_half_increment_sub_derivative_le hf hD z e a
    simpa only [e, Pi.norm_single, norm_one, one_pow, mul_one, ha,
      show (C : ℝ) / 2 * (4 / (m : ℝ)) = 2 * (C : ℝ) / m by ring] using h
  rw [normalizedBoolBlocks_update, normalizedBoolBlocks_update]
  change |(f (z + ((boolToSign false - boolToSign (x i j)) / Real.sqrt m) • e) -
    f (z + ((boolToSign true - boolToSign (x i j)) / Real.sqrt m) • e)) / 2 -
    D z e / Real.sqrt m| ≤ _
  cases hbit : x i j
  · simp only [boolToSign_false, boolToSign_true, sub_self, zero_div,
      zero_smul, add_zero]
    have h := hbound (-(2 / Real.sqrt m)) (by simpa only [neg_sq] using hsq)
    rw [show -1 - (1 : ℝ) = -2 by norm_num]
    rw [neg_div]
    rw [show (f z - f (z + -(2 / Real.sqrt m) • e)) / 2 - D z e / Real.sqrt m =
      -((f (z + -(2 / Real.sqrt m) • e) - f z) / 2 -
        (-(2 / Real.sqrt m) / 2) * D z e) by ring, abs_neg]
    exact h
  · simp only [boolToSign_false, boolToSign_true, sub_self, zero_div,
      zero_smul, add_zero]
    rw [show (1 : ℝ) - -1 = 2 by norm_num]
    convert hbound (2 / Real.sqrt m) hsq using 1
    congr 1
    ring

end BooleanAnalysis.GaussianSpace
