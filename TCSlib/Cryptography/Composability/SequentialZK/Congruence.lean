/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Execution congruence on the reached histories

## Main definitions

This module introduces no definitions.

## Main results

* `Composability.exec_congr_reachable`: two executions agree up to `g` moves when the
  parties' replies agree at each active move on the histories reached by the source run.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive executions) and Theorem 175.1 (sequential composition).
-/

namespace TCSlib.Cryptography.Composability

/-- For source strategies `P`, `V`, target strategies `P2`, `V2`, mover flag `vFirst`,
common input `x`, auxiliary inputs `zP`, `zV`, source tapes `rP`, `rV`, target tapes `rP2`,
`rV2`, and move bound `g`, suppose the active source and target strategies give the same
reply on the source run's received history at every `t < g`. Then
`exec P V vFirst x zP zV rP rV g = exec P2 V2 vFirst x zP zV rP2 rV2 g`.
[PS10, §4.4].

**Proof sketch.** Induct on the move bound. The histories are empty at zero. At the next
move, the induction hypothesis identifies the two earlier transcripts, so both active
strategies read the same source history. The appropriate reply hypothesis makes the
appended messages agree, preserving equality of the transcripts. -/
theorem exec_congr_reachable (P V P2 V2 : Strategy) (vFirst : Bool)
    (x zP zV rP rV rP2 rV2 : List Bool) (g : ℕ)
    (hP : ∀ t < g, moverIsV vFirst t = false →
      P.next x zP rP (exec P V vFirst x zP zV rP rV t).1 =
        P2.next x zP rP2 (exec P V vFirst x zP zV rP rV t).1)
    (hV : ∀ t < g, moverIsV vFirst t = true →
      V.next x zV rV (exec P V vFirst x zP zV rP rV t).2 =
        V2.next x zV rV2 (exec P V vFirst x zP zV rP rV t).2) :
    exec P V vFirst x zP zV rP rV g = exec P2 V2 vFirst x zP zV rP2 rV2 g := by
  revert hP hV
  induction g with
  | zero =>
    intro _ _
    rw [exec_zero, exec_zero]
  | succ g ih =>
    intro hP hV
    have hprev := ih (fun t ht => hP t (by omega)) (fun t ht => hV t (by omega))
    -- Read both next moves on the common earlier transcript.
    rw [exec_succ, exec_succ, ← hprev]
    by_cases hm : moverIsV vFirst g = true
    · simp only [hm, if_true]
      rw [hV g (Nat.lt_succ_self g) hm]
    · simp only [Bool.not_eq_true] at hm
      simp only [hm, Bool.false_eq_true, if_false]
      rw [hP g (Nat.lt_succ_self g) hm]

end TCSlib.Cryptography.Composability
