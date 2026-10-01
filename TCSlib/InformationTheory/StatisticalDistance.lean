/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.FinDist
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical distance

The statistical (total variation) distance between two distributions on a finite type, and the
`ℓ¹`–`ℓ²` bound that turns a collision-probability estimate into a statistical-distance estimate.

That bound, `statDist_uniform_le_sqrt`, is the engine of the leftover hash lemma and of
smoothing/extractor arguments generally: collision probability is a quadratic quantity and so is
easy to compute exactly, while statistical distance is an `ℓ¹` quantity and is what security
definitions speak in; Cauchy–Schwarz is the bridge.

## Main definitions

* `TCSlib.InformationTheory.statDist`: `½ ∑ |p a - q a|`.

## Main results

* `statDist_nonneg`, `statDist_comm`, `statDist_self`, `statDist_triangle`: metric properties.
* `statDist_uniform_le_sqrt`: `statDist p uniform ≤ ½ √(|α| · collision p - 1)`.

## References

* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.1–6.2.
* [Sho09] V. Shoup, *A Computational Introduction to Number Theory and Algebra*, 2nd ed., §8.
-/

namespace TCSlib.InformationTheory

open Finset FinDist

variable {α : Type*} [Fintype α]

/-- The statistical distance (total variation distance) between two distributions:
`½ ∑ |p a - q a|`. [Vad12, §6.1] -/
noncomputable def statDist (p q : FinDist α) : ℝ := (1 / 2) * ∑ a, |p a - q a|

theorem statDist_nonneg (p q : FinDist α) : 0 ≤ statDist p q := by
  refine mul_nonneg (by norm_num) (sum_nonneg fun _ _ => abs_nonneg _)

theorem statDist_comm (p q : FinDist α) : statDist p q = statDist q p := by
  simp only [statDist]
  exact congrArg _ (sum_congr rfl fun a _ => abs_sub_comm _ _)

@[simp] theorem statDist_self (p : FinDist α) : statDist p p = 0 := by simp [statDist]

theorem statDist_triangle (p q r : FinDist α) : statDist p r ≤ statDist p q + statDist q r := by
  simp only [statDist, ← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun a _ => ?_) (by norm_num)
  exact abs_sub_le _ _ _

/-- **The `ℓ¹`–`ℓ²` bound.** A distribution whose collision probability is close to the uniform
value `1/|α|` is close to uniform in statistical distance.

**Proof sketch.** Write `d a = p a - 1/n` with `n = |α|`. Expanding the square and using
`∑ p a = 1` gives `∑ d a ^ 2 = collision p - 1/n`. Cauchy–Schwarz (Chebyshev's sum inequality in
the form `(∑ |d|) ^ 2 ≤ n ∑ d ^ 2`) then bounds `∑ |d a|` by `√(n · collision p - 1)`, and
statistical distance is half of that sum. -/
theorem statDist_uniform_le_sqrt [Nonempty α] (p : FinDist α) :
    statDist p (uniform α) ≤ (1 / 2) * Real.sqrt (Fintype.card α * collision p - 1) := by
  set n : ℝ := (Fintype.card α : ℝ) with hn_def
  have hn : (0 : ℝ) < n := by rw [hn_def]; exact_mod_cast p.card_pos
  have hn0 : n ≠ 0 := ne_of_gt hn
  -- `∑ (p a - 1/n) ^ 2 = collision p - 1/n`
  have hexp : ∑ a, (p a - n⁻¹) ^ 2 = collision p - n⁻¹ := by
    simp only [collision]
    have hterm : ∀ a : α, (p a - n⁻¹) ^ 2 = p a ^ 2 - 2 * n⁻¹ * p a + n⁻¹ ^ 2 := fun a => by ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, p.sum_prob,
      Finset.sum_const, card_univ, nsmul_eq_mul, ← hn_def]
    field_simp
    ring
  -- Cauchy–Schwarz
  have cs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset α)) (f := fun a => |p a - n⁻¹|)
  rw [card_univ, ← hn_def] at cs
  have habs : ∑ a, |p a - n⁻¹| ^ 2 = collision p - n⁻¹ := by
    rw [← hexp]
    exact sum_congr rfl fun a _ => sq_abs _
  rw [habs] at cs
  have hsq : (∑ a, |p a - n⁻¹|) ^ 2 ≤ n * collision p - 1 := by
    refine cs.trans (le_of_eq ?_)
    field_simp
  have hle : ∑ a, |p a - n⁻¹| ≤ Real.sqrt (n * collision p - 1) :=
    Real.le_sqrt_of_sq_le hsq
  simp only [statDist, uniform_apply, ← hn_def]
  exact mul_le_mul_of_nonneg_left hle (by norm_num)

end TCSlib.InformationTheory
