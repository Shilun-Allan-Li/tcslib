/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Distributions on a finite type

A lightweight, real-valued model of a probability distribution on a finite type: a nonnegative
function summing to one. This is deliberately not `PMF`, whose `ℝ≥0∞` values make subtraction
truncated and Cauchy–Schwarz awkward — and the arguments this file supports (collision
probability, the `ℓ¹`–`ℓ²` bound, the leftover hash lemma) are all differences of real numbers.

## Main definitions

* `TCSlib.InformationTheory.FinDist α`: a distribution on a finite type.
* `FinDist.uniform`, `FinDist.map`, `FinDist.prod`: the uniform distribution, pushforward along a
  function, and the product (independent pair) of two distributions.
* `FinDist.collision`: the collision probability `∑ p a ^ 2`, i.e. the chance that two
  independent samples agree.
* `FinDist.HasMinEntropy p k`: every outcome has probability at most `2 ^ (-k)`.

## Main results

* `FinDist.collision_le_of_hasMinEntropy`: min-entropy `k` bounds the collision probability by
  `2 ^ (-k)`.
* `FinDist.collision_uniform`, `FinDist.inv_card_le_collision`: the uniform distribution
  minimizes collision probability.

## References

* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.
* [Sho09] V. Shoup, *A Computational Introduction to Number Theory and Algebra*, 2nd ed., §8.
-/

namespace TCSlib.InformationTheory

open Finset

/-- A probability distribution on a finite type: nonnegative weights summing to one. -/
structure FinDist (α : Type*) [Fintype α] where
  /-- The probability assigned to each outcome. -/
  prob : α → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ a, 0 ≤ prob a
  /-- Probabilities sum to one. -/
  sum_prob : ∑ a, prob a = 1

namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β]

instance : CoeFun (FinDist α) (fun _ => α → ℝ) := ⟨FinDist.prob⟩

@[simp] theorem coe_mk (f : α → ℝ) (h₁ : ∀ a, 0 ≤ f a) (h₂ : ∑ a, f a = 1) (a : α) :
    (⟨f, h₁, h₂⟩ : FinDist α) a = f a := rfl

@[ext] theorem ext {p q : FinDist α} (h : ∀ a, p a = q a) : p = q := by
  cases p; cases q; simpa using funext h

theorem le_one (p : FinDist α) (a : α) : p a ≤ 1 := by
  rw [← p.sum_prob]
  exact single_le_sum (fun b _ => p.nonneg b) (mem_univ a)

theorem card_pos (p : FinDist α) : 0 < Fintype.card α := by
  by_contra hcon
  have hzero : Fintype.card α = 0 := by omega
  haveI : IsEmpty α := Fintype.card_eq_zero_iff.1 hzero
  have hsum := p.sum_prob
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  norm_num at hsum

instance (p : FinDist α) : Nonempty α := Fintype.card_pos_iff.1 p.card_pos

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] : FinDist α where
  prob _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := by positivity
  sum_prob := by
    have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [Finset.sum_const, card_univ, nsmul_eq_mul]
    field_simp

@[simp] theorem uniform_apply [Nonempty α] (a : α) :
    uniform α a = (Fintype.card α : ℝ)⁻¹ := rfl

/-- The pushforward of a distribution along a function. -/
def map [DecidableEq β] (f : α → β) (p : FinDist α) : FinDist β where
  prob b := ∑ a ∈ univ.filter (fun a => f a = b), p a
  nonneg _ := sum_nonneg fun a _ => p.nonneg a
  sum_prob := by
    rw [← p.sum_prob]
    exact sum_fiberwise_eq_sum_filter univ univ f p.prob ▸ (sum_fiberwise _ _ _)

@[simp] theorem map_apply [DecidableEq β] (f : α → β) (p : FinDist α) (b : β) :
    map f p b = ∑ a ∈ univ.filter (fun a => f a = b), p a := rfl

/-- The product of two distributions: an independent pair. -/
def prod (p : FinDist α) (q : FinDist β) : FinDist (α × β) where
  prob x := p x.1 * q x.2
  nonneg x := mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_prob := by
    rw [Fintype.sum_prod_type]
    simp [← Finset.mul_sum, p.sum_prob, q.sum_prob]

@[simp] theorem prod_apply (p : FinDist α) (q : FinDist β) (x : α × β) :
    prod p q x = p x.1 * q x.2 := rfl

/-- The collision probability of `p`: the probability that two independent samples from `p`
are equal. [Vad12, §6.1] -/
def collision (p : FinDist α) : ℝ := ∑ a, p a ^ 2

theorem collision_nonneg (p : FinDist α) : 0 ≤ collision p :=
  sum_nonneg fun _ _ => sq_nonneg _

@[simp] theorem collision_uniform [Nonempty α] :
    collision (uniform α) = (Fintype.card α : ℝ)⁻¹ := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [collision, uniform_apply, Finset.sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- Uniform is the distribution of least collision probability. -/
theorem inv_card_le_collision (p : FinDist α) : (Fintype.card α : ℝ)⁻¹ ≤ collision p := by
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast p.card_pos
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset α)) (f := p.prob)
  rw [p.sum_prob, card_univ] at h
  have h2 : (1 : ℝ) ≤ (Fintype.card α : ℝ) * collision p := by
    simpa [collision] using h
  rw [inv_le_iff_one_le_mul₀ hc]
  linarith [mul_comm (Fintype.card α : ℝ) (collision p)]

/-- `p` has min-entropy at least `k` when no outcome has probability more than `2 ^ (-k)`.
Stated as this bound rather than as `-logb 2 (⨆ a, p a)` so that no logarithms appear in the
hypotheses of the results that use it. [Vad12, §6.2] -/
def HasMinEntropy (p : FinDist α) (k : ℝ) : Prop := ∀ a, p a ≤ (2 : ℝ) ^ (-k)

/-- Min-entropy `k` bounds the collision probability by `2 ^ (-k)`: the chance of a collision is
at most the chance of hitting any single most-likely point.

**Proof sketch.** `∑ p a ^ 2 ≤ (max p) · ∑ p a = max p ≤ 2 ^ (-k)`. -/
theorem collision_le_of_hasMinEntropy {p : FinDist α} {k : ℝ} (h : HasMinEntropy p k) :
    collision p ≤ (2 : ℝ) ^ (-k) := by
  calc collision p = ∑ a, p a * p a := by simp [collision, sq]
    _ ≤ ∑ a, (2 : ℝ) ^ (-k) * p a :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (h a) (p.nonneg a)
    _ = (2 : ℝ) ^ (-k) := by rw [← Finset.mul_sum, p.sum_prob, mul_one]

end FinDist

end TCSlib.InformationTheory
