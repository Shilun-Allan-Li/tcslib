/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.OneWayFunctions.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Execution prefixes for sequential soundness

## Main definitions

This module introduces no definitions.

## Main results

* `Composability.exec_prefix`: each received history after `g` moves is a prefix of its
  history after `g + t` moves.
* `Composability.exec_fst_take`, `Composability.exec_snd_take`: taking the old history length
  from the later history recovers the old history.
* `Composability.uprob_adaptive_all_le`: phase success at most `s` after each prefix gives
  total success at most `s ^ q`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive executions) and Theorem 175.1 (sequential composition).
-/

namespace TCSlib.Cryptography.Composability

/-- For strategies `P`, `V`, first-mover flag `vFirst`, common input `x`, auxiliary inputs
`zP`, `zV`, tapes `rP`, `rV`, and move counts `g`, `t`, both components of
`exec P V vFirst x zP zV rP rV g` are prefixes of the corresponding components after `g + t`
moves. [PS10, §4.4].
`(exec P V vFirst x zP zV rP rV g).1 <+: (exec P V vFirst x zP zV rP rV (g + t)).1 ∧ (exec P V
vFirst x zP zV rP rV g).2 <+: (exec P V vFirst x zP zV rP rV (g + t)).2`.

**Proof sketch.** Induct on the additional moves. Each move appends one message to exactly
one received history, so prefix transitivity preserves both earlier histories. -/
theorem exec_prefix (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool)
    (g t : ℕ) :
    (exec P V vFirst x zP zV rP rV g).1 <+:
        (exec P V vFirst x zP zV rP rV (g + t)).1 ∧
      (exec P V vFirst x zP zV rP rV g).2 <+:
        (exec P V vFirst x zP zV rP rV (g + t)).2 := by
  induction t with
  | zero => simp only [Nat.add_zero, List.prefix_rfl, and_self]
  | succ t ih =>
    rw [Nat.add_succ, exec_succ]
    by_cases hm : moverIsV vFirst (g + t) = true
    · simp only [hm, if_true]
      exact ⟨List.prefix_append_of_prefix ih.1, ih.2⟩
    · simp only [hm]
      exact ⟨ih.1, List.prefix_append_of_prefix ih.2⟩

/-- For `P`, `V`, `vFirst`, `x`, `zP`, `zV`, `rP`, `rV`, `g`, `t`, taking the length of
`(exec P V vFirst x zP zV rP rV g).1` from the first component after `g + t` moves gives
`(exec P V vFirst x zP zV rP rV g).1`.
`(exec P V vFirst x zP zV rP rV (g + t)).1.take (exec P V vFirst x zP zV rP rV g).1.length = (exec P
V vFirst x zP zV rP rV g).1`. -/
theorem exec_fst_take (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool)
    (g t : ℕ) :
    (exec P V vFirst x zP zV rP rV (g + t)).1.take
        (exec P V vFirst x zP zV rP rV g).1.length =
      (exec P V vFirst x zP zV rP rV g).1 :=
  (List.prefix_iff_eq_take.mp (exec_prefix P V vFirst x zP zV rP rV g t).1).symm

/-- For `P`, `V`, `vFirst`, `x`, `zP`, `zV`, `rP`, `rV`, `g`, `t`, taking the length of
`(exec P V vFirst x zP zV rP rV g).2` from the second component after `g + t` moves gives
`(exec P V vFirst x zP zV rP rV g).2`.
`(exec P V vFirst x zP zV rP rV (g + t)).2.take (exec P V vFirst x zP zV rP rV g).2.length = (exec P
V vFirst x zP zV rP rV g).2`. -/
theorem exec_snd_take (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool)
    (g t : ℕ) :
    (exec P V vFirst x zP zV rP rV (g + t)).2.take
        (exec P V vFirst x zP zV rP rV g).2.length =
      (exec P V vFirst x zP zV rP rV g).2 :=
  (List.prefix_iff_eq_take.mp (exec_prefix P V vFirst x zP zV rP rV g t).2).symm

/-- For `q` phases, a nonnegative bound `s`, and tests `Good i prefix fresh`, if
`Pr[fresh, Good i prefix fresh] ≤ s` for every `i < q` and every earlier prefix, then
`Pr[coins : Fin q → α, ∀ i, Good i (coins restricted below i) (coins i)] ≤ s ^ q`.
[PS10, Theorem 175.1, sequential soundness].

**Proof sketch.** Induct on the phase count, splitting the uniform tuple into its strict
prefix and last coordinate with `Fin.snocEquiv`. The event for all phases implies success
of the prefix together with the last phase. Conditional on a fixed prefix, the last phase
succeeds with probability at most `s`. The published product bound therefore multiplies
the prefix probability by `s`, and the induction hypothesis supplies the remaining power. -/
theorem uprob_adaptive_all_le {α : Type*} [Fintype α] (q : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (Good : (i : ℕ) → (Fin i → α) → α → Prop)
    (hGood : ∀ i < q, ∀ pre, uprob (Good i pre) ≤ s) :
    uprob (fun coins : Fin q → α => ∀ i : Fin q,
      Good i (fun j => coins (Fin.castLE i.isLt.le j)) (coins i)) ≤ s ^ q := by
  revert hGood
  induction q with
  | zero =>
    intro _
    simpa only [pow_zero] using (uprob_le_one
      (fun coins : Fin 0 → α => ∀ i : Fin 0,
        Good i (fun j => coins (Fin.castLE i.isLt.le j)) (coins i)))
  | succ q ih =>
    intro hGood
    -- Split the final fresh coordinate from the earlier uniform tuple.
    let e : (Fin q → α) × α ≃ (Fin (q + 1) → α) :=
      (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => α))
    have he (a : (Fin q → α) × α) : e a = Fin.snoc a.1 a.2 := rfl
    rw [← uprob_comp_equiv e]
    have hmono :
        uprob (fun a : (Fin q → α) × α => ∀ i : Fin (q + 1),
          Good i (fun j => (e a) (Fin.castLE i.isLt.le j)) ((e a) i)) ≤
        uprob (fun a : (Fin q → α) × α =>
          (∀ i : Fin q, Good i (fun j => a.1 (Fin.castLE i.isLt.le j)) (a.1 i)) ∧
            Good q a.1 a.2) := by
      apply uprob_mono
      intro a ha
      rw [he] at ha
      constructor
      · intro i
        have hi := ha (Fin.castSucc i)
        have hpre :
            (fun j : Fin i => (Fin.snoc a.1 a.2 : Fin (q + 1) → α)
              (Fin.castLE (Fin.castSucc i).isLt.le j)) =
            (fun j => a.1 (Fin.castLE i.isLt.le j)) := by
          funext j
          have hj : (Fin.castLE (Fin.castSucc i).isLt.le j : Fin (q + 1)) =
              Fin.castSucc (Fin.castLE i.isLt.le j) := Fin.ext rfl
          rw [hj, Fin.snoc_castSucc]
        have hi' : Good i
            (fun j : Fin i => (Fin.snoc a.1 a.2 : Fin (q + 1) → α)
              (Fin.castLE (Fin.castSucc i).isLt.le j))
            ((Fin.snoc a.1 a.2 : Fin (q + 1) → α) (Fin.castSucc i)) := hi
        rw [hpre, Fin.snoc_castSucc] at hi'
        exact hi'
      · have hi := ha (Fin.last q)
        have hpre :
            (fun j : Fin q => (Fin.snoc a.1 a.2 : Fin (q + 1) → α)
              (Fin.castLE (Fin.last q).isLt.le j)) =
            a.1 := by
          funext j
          have hj : (Fin.castLE (Fin.last q).isLt.le j : Fin (q + 1)) =
              Fin.castSucc j := Fin.ext rfl
          rw [hj, Fin.snoc_castSucc]
        have hi' : Good q
            (fun j : Fin q => (Fin.snoc a.1 a.2 : Fin (q + 1) → α)
              (Fin.castLE (Fin.last q).isLt.le j))
            ((Fin.snoc a.1 a.2 : Fin (q + 1) → α) (Fin.last q)) := hi
        rw [hpre, Fin.snoc_last] at hi'
        exact hi'
    -- Bound the last conditional success, then apply the prefix induction hypothesis.
    have hbound := OneWay.uprob_and_le_mul
      (fun pre : Fin q → α => ∀ i : Fin q,
        Good i (fun j => pre (Fin.castLE i.isLt.le j)) (pre i))
      (fun a : (Fin q → α) × α => Good q a.1 a.2)
      (fun pre _ => hGood q (Nat.lt_succ_self q) pre)
    have hih := ih (fun i hi pre => hGood i (by omega) pre)
    calc _ ≤ _ := hmono
         _ ≤ _ := hbound
         _ ≤ s * s ^ q := mul_le_mul_of_nonneg_left hih hs
         _ = s ^ (q + 1) := by rw [pow_succ]; ring

end TCSlib.Cryptography.Composability
