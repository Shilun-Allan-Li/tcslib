/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Experiments
import Mathlib.Data.Fintype.BigOperators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probability toolkit for one-way function reductions

The reductions of [Gar26, Chapter 2] manipulate uniform probabilities in a handful of
recurring ways: averaging a pointwise bound, conditioning on a bad set, splitting off a
uniform index, planting an input into a uniform tuple, and multiplying probabilities of
independent coordinates. This file proves these facts once, on top of the uniform
probability `uprob` and expectation `uexp` of `Foundations/Probability.lean`.

## Main definitions

None; this file only proves laws about `uprob` and `uexp`.

## Main results

* `uexp_mono`, `uexp_add`, `uexp_const`, `uexp_indicator`: laws of the uniform average.
* `uprob_and_le_mul`: conditioning on a set `S` on which every section has probability
  at most `θ` costs at most `θ · Pr[S]`.
* `sum_uprob_eq_card_mul`: a sum over a uniform index is `q` times a probability.
* `uprob_pi_forall`: independent coordinates multiply.
* `uprob_update`: planting a fresh uniform value into a uniform tuple leaves it uniform.
* `uprob_eq_one_div_card`: a uniform element hits a fixed point with probability
  `1 / |α|`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Chapter 2 (the computations in §2.2.2 and §2.3).
-/

namespace TCSlib.Cryptography.OneWay

open Finset TCSlib.Cryptography

variable {α β ρ : Type*} [Fintype α] [Fintype β] [Fintype ρ]

/-- Two events that hold for the same elements have the same probability. -/
theorem uprob_congr {p q : α → Prop} (h : ∀ a, p a ↔ q a) : uprob p = uprob q := by
  rw [show p = q from funext fun a => propext (h a)]

/-- A pointwise smaller function has a smaller average. -/
theorem uexp_mono {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : uexp f ≤ uexp g := by
  unfold uexp
  exact div_le_div_of_nonneg_right (sum_le_sum fun a _ => h a) (Nat.cast_nonneg _)

/-- The average of a sum is the sum of the averages. -/
theorem uexp_add (f g : α → ℝ) : uexp (fun a => f a + g a) = uexp f + uexp g := by
  unfold uexp
  rw [sum_add_distrib, add_div]

/-- The average of a constant times a function is the constant times the average. -/
theorem uexp_const_mul (c : ℝ) (f : α → ℝ) : uexp (fun a => c * f a) = c * uexp f := by
  unfold uexp
  rw [← mul_sum, mul_div_assoc]

/-- The average of a constant over a nonempty type is that constant. -/
theorem uexp_const [Nonempty α] (c : ℝ) : uexp (fun _ : α => c) = c := by
  unfold uexp
  have : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- The average of `c` times the indicator of `p` is `c` times the probability of `p`. -/
theorem uexp_indicator (p : α → Prop) [DecidablePred p] (c : ℝ) :
    uexp (fun a => if p a then c else 0) = c * uprob p := by
  rw [uprob_eq_uexp, ← uexp_const_mul]
  congr 1
  funext a
  split_ifs <;> simp

/-- Conditioning on a bad set: if every `a` in `S` has a section of `p` of probability at
most `θ`, then `S a ∧ p (a, b)` has probability at most `θ · Pr[S]`. [Gar26, §2.3, proof
of Theorem 2.1, the step `Pr[x ∈ S ∧ E] ≤ Pr[x ∈ S] · Pr[E | x ∈ S]`].

**Proof sketch.** Average over `a` the section probabilities: the section of the event is
empty off `S` and has probability at most `θ` on `S`. -/
theorem uprob_and_le_mul (S : α → Prop) (p : α × β → Prop) {θ : ℝ}
    (h : ∀ a, S a → uprob (fun b => p (a, b)) ≤ θ) :
    uprob (fun z : α × β => S z.1 ∧ p z) ≤ θ * uprob S := by
  classical
  rw [uprob_prod, ← uexp_indicator]
  apply uexp_mono
  intro a
  by_cases ha : S a
  · simp only [ha, true_and, if_true]
    exact h a ha
  · simp only [ha, false_and, if_false]
    rw [uprob_false]

/-- Splitting off a uniform index: the sum over `i` of the probabilities of the events
`p i` is `|ι|` times the probability of `p i ω` for uniform `(i, ω)`. [Gar26, §2.3, proof
of Theorem 2.1, the step introducing the uniform index `i`]. -/
theorem sum_uprob_eq_card_mul (p : β → α → Prop) :
    ∑ i, uprob (p i) = Fintype.card β * uprob (fun z : β × α => p z.1 z.2) := by
  rw [uprob_prod]
  unfold uexp
  rcases Nat.eq_zero_or_pos (Fintype.card β) with h | h
  · rw [Fintype.card_eq_zero_iff] at h
    simp [Finset.univ_eq_empty]
  · have : (Fintype.card β : ℝ) ≠ 0 := by positivity
    field_simp

/-- Independent coordinates multiply: the probability that every coordinate of a uniform
tuple satisfies `p` is the `|ι|`-th power of the probability of `p`. [Gar26, §2.3, proof
of Theorem 2.1, `Pr[∀ i : xᵢ ∉ S] = (1 - Pr[S])^q`]. -/
theorem uprob_pi_forall {ι : Type*} [Fintype ι] [DecidableEq ι] (p : α → Prop) :
    uprob (fun xs : ι → α => ∀ i, p (xs i)) = uprob p ^ Fintype.card ι := by
  unfold uprob
  rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun _ a => p a)), Nat.card_pi,
    prod_const, card_univ, Fintype.card_fun, Nat.cast_pow, Nat.cast_pow, div_pow]

/-- Planting a fresh uniform value `x` at position `i` of a uniform tuple `xs` (with
further independent coins `r`) yields a uniform tuple. [Gar26, §2.3, proof of
Theorem 2.1: "`x` is distributed as `xᵢ`"].

**Proof sketch.** The map `(x, (xs, r)) ↦ ((update xs i x, r), xs i)` is a bijection,
with inverse `((zs, r), a) ↦ (zs i, (update zs i a, r))`; the planted tuple is its first
component, and the forgotten coordinate `a` is irrelevant to the event. -/
theorem uprob_update {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty α] (i : ι)
    (P : (ι → α) → ρ → Prop) :
    uprob (fun z : α × ((ι → α) × ρ) => P (Function.update z.2.1 i z.1) z.2.2) =
      uprob (fun w : (ι → α) × ρ => P w.1 w.2) := by
  let e : α × ((ι → α) × ρ) ≃ ((ι → α) × ρ) × α :=
    { toFun := fun z => ((Function.update z.2.1 i z.1, z.2.2), z.2.1 i)
      invFun := fun w => (w.1.1 i, (Function.update w.1.1 i w.2, w.1.2))
      left_inv := fun z => by simp
      right_inv := fun w => by simp }
  rw [← uprob_fst (β := α) (fun w : (ι → α) × ρ => P w.1 w.2), ← uprob_comp_equiv e]
  rfl

/-- A uniform element of `α` equals a fixed point `a` with probability `1 / |α|`. -/
theorem uprob_eq_one_div_card (a : α) : uprob (fun x : α => x = a) = 1 / Fintype.card α := by
  unfold uprob
  simp

end TCSlib.Cryptography.OneWay
