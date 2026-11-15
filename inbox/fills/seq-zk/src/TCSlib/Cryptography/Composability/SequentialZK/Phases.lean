/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.Soundness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A prover with a fixed earlier transcript

## Main definitions

* `Composability.prefixProver`: a prover with its original auxiliary input, tape, and
  previously received messages fixed in advance.

## Main results

* `Composability.exec_phase_of_moves`: source replies matching arbitrary local strategies
  give a phase coupling with the fixed earlier histories.
* `Composability.exec_phase`: an execution after a fixed move offset is its earlier
  transcript followed by an execution of the prefix-hardwired prover, whenever the
  verifier's real-phase replies and the mover pattern agree.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive executions) and Theorem 175.1 (sequential composition).
-/

namespace TCSlib.Cryptography.Composability

/-- For a strategy `P`, auxiliary input `y`, fixed tape `rP`, and earlier received messages
`prior`, `prefixProver P y rP prior` has zero coins and sends
`P.next x y rP (prior ++ hist)` on `x`, any auxiliary input, any tape, and history `hist`.
[PS10, Theorem 175.1, the prover induced by a fixed earlier transcript]. -/
@[simps (config := { isSimp := false }) coins next]
def prefixProver (P : Strategy) (y rP : List Bool)
    (prior : List (List Bool)) : Strategy where
  next x _ _ hist := P.next x y rP (prior ++ hist)
  coins := .const 0

/-- For source strategies `P`, `V`, local strategies `P0`, `V0`, mover flag `vFirst`,
common input `x`, source auxiliary inputs `y`, `z` and tapes `rP`, `rV`, local auxiliary
inputs `y0`, `z0` and tapes `rP0`, `rV0`, offset `g`, and budget `k`, suppose the mover
patterns agree and each active source reply before `k` equals the local party's reply on
the source history with its pre-`g` prefix dropped. For `t ≤ k`, both source histories at
`g+t` equal their pre-`g` histories followed by the corresponding components of
`exec P0 V0 vFirst x y0 z0 rP0 rV0 t`. [PS10, Theorem 175.1, phase coupling].

**Proof sketch.** Induct on `t`. Both local histories are empty at zero. At a later move,
the induction equalities identify each full source history with its fixed earlier prefix
followed by the local history. Dropping this prefix gives the local party's received
history. The supplied active-move equation therefore gives a common next message, and
append associativity preserves both transcript decompositions. -/
theorem exec_phase_of_moves (P V P0 V0 : Strategy) (vFirst : Bool)
    (x y z rP rV y0 z0 rP0 rV0 : List Bool) (g k : ℕ)
    (hturn : ∀ t < k, moverIsV vFirst (g + t) = moverIsV vFirst t)
    (hP : ∀ t < k, moverIsV vFirst t = false →
      P.next x y rP (exec P V vFirst x y z rP rV (g + t)).1 =
        P0.next x y0 rP0
          ((exec P V vFirst x y z rP rV (g + t)).1.drop
            (exec P V vFirst x y z rP rV g).1.length))
    (hV : ∀ t < k, moverIsV vFirst t = true →
      V.next x z rV (exec P V vFirst x y z rP rV (g + t)).2 =
        V0.next x z0 rV0
          ((exec P V vFirst x y z rP rV (g + t)).2.drop
            (exec P V vFirst x y z rP rV g).2.length))
    {t : ℕ} (ht : t ≤ k) :
    (exec P V vFirst x y z rP rV (g + t)).1 =
        (exec P V vFirst x y z rP rV g).1 ++
          (exec P0 V0 vFirst x y0 z0 rP0 rV0 t).1 ∧
      (exec P V vFirst x y z rP rV (g + t)).2 =
        (exec P V vFirst x y z rP rV g).2 ++
          (exec P0 V0 vFirst x y0 z0 rP0 rV0 t).2 := by
  revert ht
  induction t with
  | zero =>
    intro _
    rw [Nat.add_zero, exec_zero]
    simp only [List.append_nil, and_self]
  | succ t ih =>
    intro ht
    have htk : t < k := by omega
    obtain ⟨ihP, ihV⟩ := ih (by omega)
    -- The source and local executions make the same kind of move.
    rw [Nat.add_succ, exec_succ, exec_succ, hturn t htk]
    by_cases hm : moverIsV vFirst t = true
    · simp only [hm, if_true]
      have hnext := hV t htk hm
      rw [ihV, List.drop_left] at hnext
      constructor
      · rw [ihP, ihV, hnext, List.append_assoc]
      · exact ihV
    · simp only [Bool.not_eq_true] at hm
      simp only [hm, Bool.false_eq_true, if_false]
      have hnext := hP t htk hm
      rw [ihP, List.drop_left] at hnext
      constructor
      · exact ihP
      · rw [ihV, ihP, hnext, List.append_assoc]

/-- For strategies `P`, `V`, `W`, mover flag `vFirst`, input `x`, auxiliary inputs `y`, `z`,
tapes `rP`, `rV`, `rW`, offset `g`, and budget `k`, suppose the mover at `g+t` equals the
mover at `t`, and at every verifier move before `k`, `V` on the full history equals `W` on
that history with the messages preceding `g` dropped. For `t ≤ k`, each received history
after `g+t` moves equals its history after `g` followed by the corresponding history of
`prefixProver P y rP (exec P V vFirst x y z rP rV g).1` against `W` for `t` moves.
[PS10, Theorem 175.1, a phase with the earlier transcript fixed].

**Proof sketch.** Apply the generic phase-coupling theorem. The supplied verifier equation
is its verifier-move premise. For the prover premise, the earlier received history is a
prefix of the current one, so prepending it to the dropped suffix recovers the full
history. The hardwired prover's published message equation gives the required reply. -/
theorem exec_phase (P V W : Strategy) (vFirst : Bool)
    (x y z rP rV rW : List Bool) (g k : ℕ)
    (hturn : ∀ t < k, moverIsV vFirst (g + t) = moverIsV vFirst t)
    (hV : ∀ t < k, moverIsV vFirst t = true →
      V.next x z rV (exec P V vFirst x y z rP rV (g + t)).2 =
        W.next x z rW
          ((exec P V vFirst x y z rP rV (g + t)).2.drop
            (exec P V vFirst x y z rP rV g).2.length))
    {t : ℕ} (ht : t ≤ k) :
    (exec P V vFirst x y z rP rV (g + t)).1 =
        (exec P V vFirst x y z rP rV g).1 ++
          (exec (prefixProver P y rP (exec P V vFirst x y z rP rV g).1)
            W vFirst x [] z [] rW t).1 ∧
      (exec P V vFirst x y z rP rV (g + t)).2 =
        (exec P V vFirst x y z rP rV g).2 ++
          (exec (prefixProver P y rP (exec P V vFirst x y z rP rV g).1)
            W vFirst x [] z [] rW t).2 := by
  apply exec_phase_of_moves P V
    (prefixProver P y rP (exec P V vFirst x y z rP rV g).1) W vFirst
    x y z rP rV [] z [] rW g k hturn ?_ hV ht
  intro t _ _
  rw [prefixProver_next]
  have hp := (exec_prefix P V vFirst x y z rP rV g t).1
  rw [List.prefix_iff_eq_append.mp hp]

end TCSlib.Cryptography.Composability
