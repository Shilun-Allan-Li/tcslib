/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.Normalization

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bounded prover messages in executions

The phase normalization for sequential composition [PS10, Theorem 175.1] fixes real phase
views because every honest prover message satisfies the common bit bound. This file reads
that fact from the public zero/successor execution equations, independently of the verifier's
behavior or any property of its tape and auxiliary input.

## Main definitions

There are no new definitions.

## Main results

* `exec_snd_bounded`: a uniform bound on the prover's next message bounds every message the
  verifier receives in any finite execution.
* `exec_snd_slice_bounded`: the bound also holds after dropping and taking messages.
* `length_encodeMsgs_exec_snd_le`: the public word-list bound applied to the execution.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity

/-- For `P,V,vFirst,x,y,z,rP,rV,B,g`, if every message `P.next x y rP hist` has length at most
`B`, then every `m ∈ (exec P V vFirst x y z rP rV g).2` has length at most `B`.

**Proof sketch.** Induct on the move count through the published execution equations. A
verifier move leaves its received list unchanged. A prover move appends exactly one message,
which satisfies the uniform next-message bound; all earlier messages satisfy the induction
hypothesis. -/
theorem exec_snd_bounded (P V : Strategy) (vFirst : Bool) (x y z rP rV : List Bool)
    (B g : ℕ) (hP : ∀ hist, (P.next x y rP hist).length ≤ B) :
    ∀ m ∈ (exec P V vFirst x y z rP rV g).2, m.length ≤ B := by
  induction g with
  | zero =>
    intro m hm
    rw [exec_zero] at hm
    cases hm
  | succ g ih =>
    intro m hm
    rw [exec_succ] at hm
    by_cases hV : moverIsV vFirst g = true
    · simp only [hV, if_true] at hm
      exact ih m hm
    · simp only [hV] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact ih m hm
      · rw [List.mem_singleton.mp hm]
        exact hP _

/-- The same next-message bound controls a received-history slice: every
`m ∈ ((exec P V vFirst x y z rP rV g).2.drop d).take t` has `m.length ≤ B` when
`∀ hist, (P.next x y rP hist).length ≤ B`. -/
theorem exec_snd_slice_bounded (P V : Strategy) (vFirst : Bool) (x y z rP rV : List Bool)
    (B g d t : ℕ) (hP : ∀ hist, (P.next x y rP hist).length ≤ B) :
    ∀ m ∈ ((exec P V vFirst x y z rP rV g).2.drop d).take t, m.length ≤ B := by
  intro m hm
  exact exec_snd_bounded P V vFirst x y z rP rV B g hP m
    (List.mem_of_mem_drop (List.mem_of_mem_take hm))

/-- If every prover message has at most `B` bits, its received-history encoding satisfies
`(Strategy.encodeMsgs (exec P V vFirst x y z rP rV g).2).length ≤
(exec P V vFirst x y z rP rV g).2.length * (2 * B + 2)`. -/
theorem length_encodeMsgs_exec_snd_le (P V : Strategy) (vFirst : Bool)
    (x y z rP rV : List Bool) (B g : ℕ)
    (hP : ∀ hist, (P.next x y rP hist).length ≤ B) :
    (Strategy.encodeMsgs (exec P V vFirst x y z rP rV g).2).length ≤
      (exec P V vFirst x y z rP rV g).2.length * (2 * B + 2) := by
  rw [encodeMsgs_eq_encWords]
  exact BinArith.length_encWords_le _ B (exec_snd_bounded P V vFirst x y z rP rV B g hP)

end TCSlib.Cryptography.SequentialZK
