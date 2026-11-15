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

/-- For strategies `P`, `V`, `W`, mover flag `vFirst`, input `x`, auxiliary inputs `y`, `z`,
tapes `rP`, `rV`, `rW`, offset `g`, and budget `k`, suppose the mover at `g+t` equals the
mover at `t`, and at every verifier move before `k`, `V` on the full history equals `W` on
that history with the messages preceding `g` dropped. For `t ≤ k`, each received history
after `g+t` moves equals its history after `g` followed by the corresponding history of
`prefixProver P y rP (exec P V vFirst x y z rP rV g).1` against `W` for `t` moves.
[PS10, Theorem 175.1, a phase with the earlier transcript fixed].

**Proof sketch.** Induct on the real-phase move count. At zero the new execution has empty
histories. A prover move agrees because the hardwired earlier history is followed by the
same local history. A verifier move agrees by the reply hypothesis after the fixed prefix
is dropped. Appending the common message preserves both transcript decompositions. -/
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
    -- Both executions make the same kind of move at the corresponding positions.
    rw [Nat.add_succ, exec_succ, exec_succ, hturn t htk]
    by_cases hm : moverIsV vFirst t = true
    · simp only [hm, if_true]
      have hnext := hV t htk hm
      rw [ihV, List.drop_left] at hnext
      constructor
      · rw [ihP, ihV, hnext, List.append_assoc]
      · exact ihV
    · simp only [hm, Bool.false_eq_true, if_false]
      constructor
      · exact ihP
      · rw [ihV, ihP, prefixProver_next, List.append_assoc]

end TCSlib.Cryptography.Composability
