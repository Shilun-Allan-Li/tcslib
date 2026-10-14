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
import Mathlib.Tactic.Linarith

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
  rw [uprob, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The probability of an event is the average of its indicator. -/
theorem uprob_eq_uexp (p : α → Prop) [DecidablePred p] :
    uprob p = uexp (fun a => if p a then (1 : ℝ) else 0) := by
  rw [uprob_eq_card_filter, uexp, Finset.sum_boole]

/-- Probabilities are nonnegative. -/
theorem uprob_nonneg (p : α → Prop) : 0 ≤ uprob p := by
  unfold uprob; positivity

/-- Probabilities are at most one. -/
theorem uprob_le_one (p : α → Prop) : uprob p ≤ 1 := by
  classical
  rw [uprob_eq_card_filter]
  exact div_le_one_of_le₀ (by exact_mod_cast card_le_univ _) (by positivity)

/-- The certain event has probability one on a nonempty type. -/
theorem uprob_true [Nonempty α] : uprob (fun _ : α => True) = 1 := by
  classical
  rw [uprob_eq_card_filter, filter_true, card_univ]
  exact div_self (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

/-- The impossible event has probability zero. -/
theorem uprob_false : uprob (fun _ : α => False) = 0 := by
  classical
  rw [uprob_eq_card_filter, filter_false, card_empty, Nat.cast_zero, zero_div]

/-- The complement of an event has probability one minus its probability.

**Proof sketch.** The elements satisfying `p` and those satisfying `¬ p` partition `α`, so
their counts add up to `|α|`. -/
theorem uprob_not [Nonempty α] (p : α → Prop) : uprob (fun a => ¬ p a) = 1 - uprob p := by
  classical
  have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h := filter_card_add_filter_neg_card_eq_card (s := univ) p
  rw [card_univ] at h
  rw [uprob_eq_card_filter, uprob_eq_card_filter, eq_sub_iff_add_eq, ← add_div,
    div_eq_one_iff_eq hc]
  exact_mod_cast (by omega : (univ.filter fun a => ¬ p a).card + (univ.filter p).card =
    Fintype.card α)

/-- An event implied by another has at least its probability. -/
theorem uprob_mono {p q : α → Prop} (h : ∀ a, p a → q a) : uprob p ≤ uprob q := by
  classical
  rw [uprob_eq_card_filter, uprob_eq_card_filter]
  gcongr with a
  exact h a

/-- Union bound for two events. -/
theorem uprob_or_le (p q : α → Prop) : uprob (fun a => p a ∨ q a) ≤ uprob p + uprob q := by
  classical
  rw [uprob_eq_card_filter, uprob_eq_card_filter, uprob_eq_card_filter, ← add_div, filter_or]
  gcongr
  exact_mod_cast card_union_le _ _

/-- Union bound for finitely many events.

**Proof sketch.** The set where some `p i` holds is the union over `i ∈ s` of the sets
where `p i` holds, and the size of a union is at most the sum of the sizes. -/
theorem uprob_exists_le {ι : Type*} (s : Finset ι) (p : ι → α → Prop) :
    uprob (fun a => ∃ i ∈ s, p i a) ≤ ∑ i ∈ s, uprob (p i) := by
  classical
  rw [uprob_eq_card_filter]
  simp_rw [uprob_eq_card_filter, ← sum_div]
  gcongr
  have : (univ.filter fun a => ∃ i ∈ s, p i a) = s.biUnion (fun i => univ.filter (p i)) := by
    ext a; simp
  rw [this]
  exact_mod_cast card_biUnion_le

/-- Probability over a product is the average over the first coordinate of the
probability of the section: Fubini for uniform distributions.

**Proof sketch.** Count the pairs satisfying `p` by first coordinate:
`|{z | p z}| / (|α| |β|) = (∑ a, |{b | p (a, b)}| / |β|) / |α|`. -/
theorem uprob_prod (p : α × β → Prop) :
    uprob p = uexp (fun a => uprob (fun b => p (a, b))) := by
  classical
  simp_rw [uexp, uprob_eq_card_filter, ← sum_div, div_div, Fintype.card_prod, Nat.cast_mul,
    mul_comm (Fintype.card β : ℝ)]
  congr 1
  simp_rw [card_filter]
  push_cast
  exact Fintype.sum_prod_type _

/-- Relabelling the sample space by a bijection preserves probabilities. In particular a
permutation of a uniform input is uniform. -/
theorem uprob_comp_equiv (e : α ≃ β) (p : β → Prop) : uprob (fun a => p (e a)) = uprob p := by
  rw [uprob, uprob, Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl)),
    Fintype.card_congr e]

/-- An event depending only on the first coordinate has the same probability on the
product.

**Proof sketch.** By `uprob_prod`, the section at `a` is the certain or the impossible
event according to `p a`, so its probability is the indicator of `p a`, whose average
is `uprob p`. -/
theorem uprob_fst [Nonempty β] (p : α → Prop) : uprob (fun z : α × β => p z.1) = uprob p := by
  classical
  rw [uprob_prod, uprob_eq_uexp]
  congr 1
  funext a
  by_cases h : p a <;> simp [h, uprob_true, uprob_false]

/-- The averaging argument: if an event on `α × β` has probability at least `ε`, then
the first coordinates whose section has probability at least `ε / 2` have probability
at least `ε / 2`. [Gar26, Lemma 2.1].

**Proof sketch.** For `ε < 0` the claim is trivial, and for empty `α` both sides vanish.
Otherwise every section has probability at most `[a is good] + ε / 2`: a good `a` has
section probability at most `1`, a bad one below `ε / 2`. Averaging over `a` with Fubini
(`uprob_prod`) gives `ε ≤ uprob p ≤ Pr[good] + ε / 2`. -/
theorem half_le_uprob_good (p : α × β → Prop) {ε : ℝ} (h : ε ≤ uprob p) :
    ε / 2 ≤ uprob (fun a => ε / 2 ≤ uprob (fun b => p (a, b))) := by
  classical
  rcases lt_or_ge ε 0 with hε | hε
  · linarith [uprob_nonneg (fun a => ε / 2 ≤ uprob (fun b => p (a, b)))]
  rcases isEmpty_or_nonempty α with hα | hα
  · have : uprob p = 0 := by
      rw [uprob, Fintype.card_eq_zero, Nat.cast_zero, div_zero]
    linarith [uprob_nonneg (fun a => ε / 2 ≤ uprob (fun b => p (a, b)))]
  have hc : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  rw [uprob_prod, uexp] at h
  rw [uprob_eq_uexp, uexp]
  have hpt : ∀ a, uprob (fun b => p (a, b)) ≤
      (if ε / 2 ≤ uprob (fun b => p (a, b)) then (1 : ℝ) else 0) + ε / 2 := by
    intro a
    split_ifs with hg
    · linarith [uprob_le_one (fun b => p (a, b))]
    · linarith
  have hsum := sum_le_sum (fun a (_ : a ∈ univ) => hpt a)
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at hsum
  rw [le_div_iff₀ hc] at h ⊢
  linarith

/-- The hybrid argument, telescoping form: the gap between the ends of a chain is at
most the sum of the gaps between neighbours. [Gar26, proof of Lemma 3.3].

**Proof sketch.** Induction on `t` with the triangle inequality
`|P 0 - P (t+1)| ≤ |P 0 - P t| + |P t - P (t+1)|`. -/
theorem abs_sub_le_sum_hybrids (P : ℕ → ℝ) (t : ℕ) :
    |P 0 - P t| ≤ ∑ i ∈ range t, |P i - P (i + 1)| := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ]
    exact (abs_sub_le _ _ _).trans (add_le_add_right ih _)

/-- The hybrid argument: in a chain of `t ≥ 1` steps some neighbouring pair is at least
a `1 / t` fraction of the end-to-end gap apart. [Gar26, proof of Lemma 3.3].

**Proof sketch.** Otherwise the telescoping bound gives a sum below `t · (gap / t)`. -/
theorem exists_hybrid_gap (P : ℕ → ℝ) {t : ℕ} (ht : 0 < t) :
    ∃ k < t, |P 0 - P t| / t ≤ |P k - P (k + 1)| := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ i ∈ range t, |P i - P (i + 1)| < ∑ _i ∈ range t, |P 0 - P t| / t :=
    sum_lt_sum_of_nonempty (nonempty_range_iff.2 ht.ne') fun i hi => hcon i (mem_range.1 hi)
  have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.2 ht.ne'
  rw [sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ htR] at hlt
  linarith [abs_sub_le_sum_hybrids P t]

end TCSlib.Cryptography
