/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.InformationTheory.FinDist
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Finset.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Universal hash families

A family `f : S → α → β` of hash functions is *universal* when a random member maps any two
distinct points to the same image with probability at most `1 / |β|` — the collision probability
of a truly random function. Universality is a purely combinatorial (counting) condition, which is
why it can be met unconditionally, and it is exactly the hypothesis the leftover hash lemma needs.

## Main definitions

* `TCSlib.InformationTheory.IsUniversal`: the defining collision bound.

## Main results

* `isUniversal_affine`: the affine family `x ↦ a * x + b` over a field is universal.
* `sum_sq_fiber`: the combinatorial identity converting a sum of squared fibre weights into a sum
  over colliding pairs; this is what lets a universality hypothesis bound a collision
  probability.

## References

* [CW79] J.L. Carter, M.N. Wegman, *Universal classes of hash functions*, JCSS 18(2), 1979.
* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §3.5, §6.2.
-/

namespace TCSlib.InformationTheory

open Finset

variable {S α β : Type*} [Fintype S] [Fintype α] [Fintype β]

/-- `f` is a universal family of hash functions: for any two distinct points, the fraction of
seeds under which they collide is at most `1 / |β|`. [CW79], [Vad12, §3.5] -/
def IsUniversal [DecidableEq β] (f : S → α → β) : Prop :=
  ∀ x y : α, x ≠ y →
    ((univ.filter (fun s => f s x = f s y)).card : ℝ) ≤ (Fintype.card S : ℝ) / Fintype.card β

/-- **The affine family is universal.** Over a field, `(a, b) ↦ (x ↦ a * x + b)` is a universal
family; two distinct points collide only when `a = 0`, which is a `1 / |F|` fraction of seeds.
[CW79], [Vad12, §3.5] -/
theorem isUniversal_affine (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    IsUniversal (S := F × F) (α := F) (β := F) (fun s x => s.1 * x + s.2) := by
  intro x y hxy
  have hcard : (0 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨x⟩
  have hset : (univ.filter (fun s : F × F => s.1 * x + s.2 = s.1 * y + s.2))
      = ({(0 : F)} ×ˢ (univ : Finset F)) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
    constructor
    · intro h
      have : a * (x - y) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with ha | hxy'
      · exact ⟨ha, trivial⟩
      · exact absurd (sub_eq_zero.1 hxy') hxy
    · rintro ⟨rfl, -⟩
      ring
  rw [hset, card_product, card_singleton, card_univ, one_mul, Fintype.card_prod]
  push_cast
  rw [le_div_iff₀ hcard]

/-- Grouping a weighted sum by the fibres of `g` and squaring is the same as summing the weight
products over all colliding pairs. This is the identity that turns a collision-probability
computation into a counting problem about the hash family. -/
theorem sum_sq_fiber [DecidableEq β] (g : α → β) (w : α → ℝ) :
    ∑ y, (∑ x ∈ univ.filter (fun x => g x = y), w x) ^ 2
      = ∑ x, ∑ x', if g x = g x' then w x * w x' else 0 := by
  have h1 : ∀ y : β, (∑ x ∈ univ.filter (fun x => g x = y), w x)
      = ∑ x, if g x = y then w x else 0 := fun y => Finset.sum_filter _ _
  simp_rw [h1, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  simp_rw [ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [mem_univ, if_true]
  by_cases h : g x = g x' <;> simp [h, eq_comm]

end TCSlib.InformationTheory
