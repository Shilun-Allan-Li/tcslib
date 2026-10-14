/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform probability on finite types

Every probability in the concrete layer of the cryptography development is the
probability of an event under the uniform distribution on a finite type: inputs, keys
and coin strings are uniform, and an experiment's sample space is the product of their
types. So probabilities are exact counts, `uprob p = |{a | p a}| / |α|`, and
expectations are averages. Distributions that are not uniform arise as pushforwards
of uniform coins.

## Main definitions

* `uprob p`: the probability that a uniformly random element satisfies `p`.
* `uexp f`: the average of a real function over a finite type.

## Main results

* `uprob_nonneg`, `uprob_le_one`, `uprob_not`, `uprob_mono`, `uprob_or_le`,
  `uprob_exists_le`: basic laws and the union bound.
* `uprob_prod`: probability over a product is the average of the probabilities of
  the sections.
* `uprob_comp_equiv`: probability is invariant under relabelling by a bijection.
* `half_le_uprob_good`: the averaging argument — if an event has probability at least
  `ε`, then at least an `ε / 2` fraction of first coordinates have a section of
  probability at least `ε / 2`.
* `abs_sub_le_sum_hybrids`, `exists_hybrid_gap`: the hybrid argument for a chain of
  probabilities.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Lemma 2.1) and §3.2 (proof of Lemma 3.3).
-/

namespace TCSlib.Cryptography

open Finset

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The probability that a uniformly random element of the finite type `α` satisfies `p`,
the number of elements satisfying `p` divided by the number of elements. -/
noncomputable def uprob (p : α → Prop) : ℝ :=
  (Nat.card {a // p a} : ℝ) / Fintype.card α

/-- The average of a real function over the finite type `α`, its expectation under the
uniform distribution. -/
noncomputable def uexp (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

/-- With decidable `p`, the probability counts the elements of the filter. -/
theorem uprob_eq_card_filter (p : α → Prop) [DecidablePred p] :
    uprob p = ((univ.filter p).card : ℝ) / Fintype.card α := by
  sorry

/-- The probability of an event is the average of its indicator. -/
theorem uprob_eq_uexp (p : α → Prop) [DecidablePred p] :
    uprob p = uexp (fun a => if p a then (1 : ℝ) else 0) := by
  sorry

/-- Probabilities are nonnegative. -/
theorem uprob_nonneg (p : α → Prop) : 0 ≤ uprob p := by
  sorry

/-- Probabilities are at most one. -/
theorem uprob_le_one (p : α → Prop) : uprob p ≤ 1 := by
  sorry

/-- The certain event has probability one on a nonempty type. -/
theorem uprob_true [Nonempty α] : uprob (fun _ : α => True) = 1 := by
  sorry

/-- The impossible event has probability zero. -/
theorem uprob_false : uprob (fun _ : α => False) = 0 := by
  sorry

/-- The complement of an event has probability one minus its probability. -/
theorem uprob_not [Nonempty α] (p : α → Prop) : uprob (fun a => ¬ p a) = 1 - uprob p := by
  sorry

/-- An event implied by another has at least its probability. -/
theorem uprob_mono {p q : α → Prop} (h : ∀ a, p a → q a) : uprob p ≤ uprob q := by
  sorry

/-- Union bound for two events. -/
theorem uprob_or_le (p q : α → Prop) : uprob (fun a => p a ∨ q a) ≤ uprob p + uprob q := by
  sorry

/-- Union bound for finitely many events. -/
theorem uprob_exists_le {ι : Type*} (s : Finset ι) (p : ι → α → Prop) :
    uprob (fun a => ∃ i ∈ s, p i a) ≤ ∑ i ∈ s, uprob (p i) := by
  sorry

/-- Probability over a product is the average over the first coordinate of the
probability of the section: Fubini for uniform distributions. -/
theorem uprob_prod (p : α × β → Prop) :
    uprob p = uexp (fun a => uprob (fun b => p (a, b))) := by
  sorry

/-- Relabelling the sample space by a bijection preserves probabilities. In particular a
permutation of a uniform input is uniform. -/
theorem uprob_comp_equiv (e : α ≃ β) (p : β → Prop) : uprob (fun a => p (e a)) = uprob p := by
  sorry

/-- An event depending only on the first coordinate has the same probability on the
product. -/
theorem uprob_fst [Nonempty β] (p : α → Prop) : uprob (fun z : α × β => p z.1) = uprob p := by
  sorry

/-- The averaging argument: if an event on `α × β` has probability at least `ε`, then
the first coordinates whose section has probability at least `ε / 2` have probability
at least `ε / 2`. [Gar26, Lemma 2.1].

**Proof sketch.** Otherwise split the probability over good and bad first coordinates:
good ones contribute less than `ε / 2`, and bad ones have sections below `ε / 2`, so the
total is below `ε`. -/
theorem half_le_uprob_good (p : α × β → Prop) {ε : ℝ} (h : ε ≤ uprob p) :
    ε / 2 ≤ uprob (fun a => ε / 2 ≤ uprob (fun b => p (a, b))) := by
  sorry

/-- The hybrid argument, telescoping form: the gap between the ends of a chain is at
most the sum of the gaps between neighbours. [Gar26, proof of Lemma 3.3]. -/
theorem abs_sub_le_sum_hybrids (P : ℕ → ℝ) (t : ℕ) :
    |P 0 - P t| ≤ ∑ i ∈ range t, |P i - P (i + 1)| := by
  sorry

/-- The hybrid argument: in a chain of `t ≥ 1` steps some neighbouring pair is at least
a `1 / t` fraction of the end-to-end gap apart. [Gar26, proof of Lemma 3.3].

**Proof sketch.** Otherwise the telescoping bound gives a sum below `t · (gap / t)`. -/
theorem exists_hybrid_gap (P : ℕ → ℝ) {t : ℕ} (ht : 0 < t) :
    ∃ k < t, |P 0 - P t| / t ≤ |P k - P (k + 1)| := by
  sorry

end TCSlib.Cryptography
