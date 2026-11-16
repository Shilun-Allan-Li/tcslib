/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Sampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Averaging statistical phase comparisons over a shared prefix

The hybrid proof of sequential zero-knowledge composition [PS10, Theorem 175.1] conditions
on a common earlier prefix. A pointwise statistical bound survives averaging over the seed
that determines that prefix. The nonnegative error premise also covers an empty prefix seed
space, where the pointwise hypothesis is vacuous.

## Main definitions

There are no new definitions.

## Main results

* `statClose_average`: a common nonnegative pointwise bound remains valid after averaging
  both samplers over the same independent prefix seed.
* `statClose_chain`: `q` consecutive comparisons of error `δ` give error `q * δ`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
-/

namespace TCSlib.Cryptography.SequentialZK

/-- Averaging over a shared seed preserves a nonnegative statistical bound: for `0 ≤ δ` and
`∀ a, StatClose (F a) (G a) δ`, the samplers `(a,b) ↦ F a b` and `(a,c) ↦ G a c` are
`δ`-close. No seed type is required to be nonempty.

**Proof sketch.** Express each test probability as an average over the shared seed. Each
conditional difference is bounded by `δ`, so the public bound on differences of averages
applies. -/
theorem statClose_average {α β γ O : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {F : α → β → O} {G : α → γ → O} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ a, StatClose (F a) (G a) δ) :
    StatClose (fun r : α × β => F r.1 r.2) (fun r : α × γ => G r.1 r.2) δ := by
  refine (statClose_iff _ _ _).2 ?_
  intro T
  rw [uprob_prod, uprob_prod]
  exact abs_uexp_sub_le hδ fun a => (h a).abs_uprob_sub_le T

/-- A chain of `q` statistical comparisons adds the errors: if
`∀ i < q, StatClose (f i) (f (i + 1)) δ`, then
`StatClose (f 0) (f q) ((q : ℝ) * δ)`. The case `q = 0` needs no sign premise on `δ`.

**Proof sketch.** Induct on the chain length. The empty chain is reflexive with error zero;
append the last comparison using the public triangle inequality. -/
theorem statClose_chain {Ω O : Type*} [Fintype Ω] (f : ℕ → Ω → O) (q : ℕ) (δ : ℝ)
    (h : ∀ i < q, StatClose (f i) (f (i + 1)) δ) :
    StatClose (f 0) (f q) ((q : ℝ) * δ) := by
  revert h
  induction q with
  | zero =>
    intro _
    simpa only [Nat.cast_zero, zero_mul] using StatClose.refl (f 0)
  | succ q ih =>
    intro h
    have hprev := ih fun i hi => h i (Nat.lt_succ_of_lt hi)
    simpa only [Nat.cast_succ, add_mul, one_mul] using
      hprev.trans (h q (Nat.lt_succ_self q))

end TCSlib.Cryptography.SequentialZK
