/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Operations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compatibility names for the vendored programming layer

The files of `TCSlib/Programs/` are vendored from [AFM26], which builds on Lean and Mathlib v4.33.1.
Three names that those files use are absent at our v4.25.0 pin, under these names. This file
provides them, each proved from the lemma our pin has. **Remove each at the Mathlib bump that
provides it** (the build then reports a duplicate declaration).

## Main results

* `List.map_coe_finRange_eq_range`: the newer name of `List.map_coe_finRange`.
* `List.Pairwise.merge`: merging two lists sorted by `≤` gives a sorted list (core's
  `List.sorted_merge`).
* `Set.mem_ofPred_eq`: the newer name of `Set.mem_setOf_eq`.

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit
  e1a4e6508154ea59f030480661590a9fe3018011, Apache-2.0.
-/

/-- Mapping the values of `List.finRange n` gives `List.range n`: the newer name of
`List.map_coe_finRange`, which our Mathlib pin has under the old name. -/
theorem List.map_coe_finRange_eq_range (n : ℕ) :
    (List.finRange n).map (fun i : Fin n => (i : ℕ)) = List.range n :=
  List.map_coe_finRange n

/-- Merging two lists that are sorted by `≤` gives a list that is sorted by `≤`. This is core's
`List.sorted_merge`, stated for the boolean comparison that `List.merge` uses by default. -/
theorem List.Pairwise.merge {α : Type*} [LinearOrder α] {l₁ l₂ : List α}
    (h₁ : l₁.Pairwise (· ≤ ·)) (h₂ : l₂.Pairwise (· ≤ ·)) : (l₁.merge l₂).Pairwise (· ≤ ·) := by
  have := List.sorted_merge (le := fun a b : α => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact le_trans hab hbc)
    (fun a b => by simpa using le_total a b) l₁ l₂ (by simpa using h₁) (by simpa using h₂)
  simpa using this

/-- Membership in a set given by a predicate is the predicate: the newer name of
`Set.mem_setOf_eq`. -/
theorem Set.mem_ofPred_eq {α : Type*} {x : α} {p : α → Prop} : (x ∈ {y | p y}) = p x := rfl
