/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.Statistical
import Mathlib.Data.Fin.Tuple.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical accumulation for caller-supplied sampler recursions

Sequential zero-knowledge composition [PS10, Theorem 175.1] compares two recursively sampled
prefixes. This file assumes their zero and snoc equations as public contracts, and proves
that a common one-step statistical bound accumulates linearly. It defines no recursion,
loop, simulator, or computational host.

## Main definitions

There are no new definitions.

## Main results

* `statClose_recursion`: caller-supplied real and simulated samplers, with a common initial
  state and `δ`-close updates at every state, are `q * δ`-close after `q` updates.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
-/

namespace TCSlib.Cryptography.SequentialZK

/-- For families `realFamily q` and `simFamily q` with common initial state `initial` and
supplied zero/snoc equations for `realStep` and `simStep`, if `0 ≤ δ` and
`∀ i < q, ∀ state, StatClose (realStep i state) (simStep i state) δ`, then
`StatClose (realFamily q) (simFamily q) ((q : ℝ) * δ)`. The state type is arbitrary and the
finite coin types need not be nonempty.

**Proof sketch.** Induct on the number of updates. The zero equations give the same constant
sampler on the unique empty coin table. At the successor step, first replace only the last
real update by its simulated update, averaging its `δ` bound over the common real prefix.
Then apply the induction hypothesis to the prefixes and the public randomized postprocessing
reader to their common simulated last update. The triangle inequality adds `δ + qδ`.
The snoc equivalences identify a prefix and a last coin with the full coin table. -/
theorem statClose_recursion {α β State : Type*} [Fintype α] [Fintype β]
    (realFamily : (q : ℕ) → (Fin q → α) → State)
    (simFamily : (q : ℕ) → (Fin q → β) → State) (initial : State)
    (realStep : ℕ → State → α → State) (simStep : ℕ → State → β → State)
    (real_zero : ∀ r, realFamily 0 r = initial)
    (sim_zero : ∀ r, simFamily 0 r = initial)
    (real_snoc : ∀ q r a, realFamily (q + 1) (Fin.snoc r a) =
      realStep q (realFamily q r) a)
    (sim_snoc : ∀ q r b, simFamily (q + 1) (Fin.snoc r b) =
      simStep q (simFamily q r) b)
    (q : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hstep : ∀ i < q, ∀ state, StatClose (realStep i state) (simStep i state) δ) :
    StatClose (realFamily q) (simFamily q) ((q : ℝ) * δ) := by
  classical
  revert hstep
  induction q with
  | zero =>
    intro _
    letI : Nonempty (Fin 0 → α) := ⟨Fin.elim0⟩
    letI : Nonempty (Fin 0 → β) := ⟨Fin.elim0⟩
    refine (statClose_iff _ _ _).2 ?_
    intro T
    by_cases hT : T initial
    · simp only [real_zero, sim_zero, hT, uprob_true, Nat.cast_zero, zero_mul,
        sub_self, abs_zero, le_refl]
    · simp only [real_zero, sim_zero, hT, uprob_false, Nat.cast_zero, zero_mul,
        sub_self, abs_zero, le_refl]
  | succ q ih =>
    intro hstep
    have hprev := ih fun i hi state => hstep i (Nat.lt_succ_of_lt hi) state
    -- Replace only the last update while preserving the common real prefix.
    have hfirst :
        StatClose (fun r : (Fin q → α) × α => realStep q (realFamily q r.1) r.2)
          (fun r : (Fin q → α) × β => simStep q (realFamily q r.1) r.2) δ :=
      statClose_average hδ fun r => hstep q (Nat.lt_succ_self q) (realFamily q r)
    -- Compare prefixes through the same randomized simulated last update.
    have hsecond :
        StatClose (fun r : (Fin q → α) × β => simStep q (realFamily q r.1) r.2)
          (fun r : (Fin q → β) × β => simStep q (simFamily q r.1) r.2) ((q : ℝ) * δ) :=
      (statClose_iff _ _ _).2 fun T =>
        hprev.abs_uprob_sub_le_prod fun state coin => T (simStep q state coin)
    -- Reindex full coin tables as their prefixes and last entries.
    let eA : (Fin (q + 1) → α) ≃ (Fin q → α) × α :=
      (Fin.snocEquiv (fun _ : Fin (q + 1) => α)).symm.trans
        (Equiv.prodComm α (Fin q → α))
    let eB : (Fin (q + 1) → β) ≃ (Fin q → β) × β :=
      (Fin.snocEquiv (fun _ : Fin (q + 1) => β)).symm.trans
        (Equiv.prodComm β (Fin q → β))
    have hfull := ((hfirst.trans hsecond).comp_equiv_left eA).comp_equiv_right eB
    have hleft : ∀ r, realStep q (realFamily q (eA r).1) (eA r).2 = realFamily (q + 1) r := by
      intro r
      change realStep q (realFamily q (Fin.init r)) (r (Fin.last q)) = realFamily (q + 1) r
      simpa only [Fin.snoc_init_self] using (real_snoc q (Fin.init r) (r (Fin.last q))).symm
    have hright : ∀ r, simStep q (simFamily q (eB r).1) (eB r).2 = simFamily (q + 1) r := by
      intro r
      change simStep q (simFamily q (Fin.init r)) (r (Fin.last q)) = simFamily (q + 1) r
      simpa only [Fin.snoc_init_self] using (sim_snoc q (Fin.init r) (r (Fin.last q))).symm
    have herror : δ + (q : ℝ) * δ = ((q + 1 : ℕ) : ℝ) * δ := by
      rw [Nat.cast_succ, add_mul, one_mul]
      exact add_comm _ _
    rw [herror] at hfull
    simpa only [hleft, hright] using hfull

end TCSlib.Cryptography.SequentialZK
