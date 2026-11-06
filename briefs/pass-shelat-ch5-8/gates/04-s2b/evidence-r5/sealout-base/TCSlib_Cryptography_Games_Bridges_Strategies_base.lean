/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Protocols
import TCSlib.Cryptography.ZeroKnowledge.Interaction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
attribute [local irreducible] TCSlib.Cryptography.exec TCSlib.Cryptography.moverIsV TCSlib.Cryptography.Protocol.outP TCSlib.Cryptography.Protocol.outV TCSlib.Cryptography.Protocol.transcriptWith TCSlib.Cryptography.Strategy.coinLen TCSlib.Cryptography.Games.ExecOutcome.swap TCSlib.Cryptography.Games.OracleComp.bind TCSlib.Cryptography.Games.OracleSpec.add TCSlib.Cryptography.Games.Party.close TCSlib.Cryptography.Games.Party.endWith TCSlib.Cryptography.Games.Party.exec TCSlib.Cryptography.Games.Party.step

/-!
# Bridge B4: next-message strategies as parties

By the ruling of 2026-11-05, the ch. 2–4 layer's next-message strategies
(`TCSlib.Cryptography.Strategy`, executed by `TCSlib.Cryptography.exec` under its decision D8)
remain the definitions of interaction, and the `Games` executor `Party.exec` is the calculus in
which their properties are proved. This file embeds a strategy with a fixed random tape as a
party, and shows that the embedded execution is D8's.

**The embedding.** A strategy's next-message function `next : received ↦ message`, with its common
input, auxiliary input and tape fixed, becomes a party that keeps its received history and the
number of moves left:
- **on its turn** (`turnParty next k M`, with `k` moves left, its own included), it sends `next M`;
- **while waiting** (`waitParty next k M`), it receives the other party's message.
- **When no moves are left,** it returns `next M`: D8's output on the complete history, which for
  the last sender equals its last message (`Protocol.outV_eq_getLast_of_moverIsV`).
- **A reply off schedule** (`none` before the end, `some` after it) returns `next M`, a total
  default. The theorems are about embedded pairs, where it never happens.

**D8's alternation from any state.** `alt nF nG k MF MG` gives the received histories of the
first mover `F` and of `G` after `k` more moves, from `(MF, MG)` with `F` to move.
`exec_eq_alt` identifies D8's `exec` with it.

## Main definitions

* `Games.Bridge.turnParty`, `Games.Bridge.waitParty`: the embedded party on its turn and while
  waiting.
* `Games.Bridge.alt`: D8's alternation from a state.

## Main results

* `Games.Bridge.exec_turnParty`: the execution of two embedded strategies with fuel `k` (the
  number of moves) is `done`, with the outputs `nF` and `nG` on their final histories under `alt`.
* `Games.Bridge.exec_eq_alt`: D8's `exec` is `alt` from the empty histories, with the roles
  ordered by the first mover.
* `Games.Bridge.exec_strategies`: hence the embedded execution of a protocol's two strategies
  returns D8's outputs `outP`, `outV`.

The traced and probabilistic forms (views, and tapes sampled first) are stated in a later part
of this file.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines, executions, views).
-/

namespace TCSlib.Cryptography.Games.Bridge

open TCSlib.Cryptography

/-- Messages and histories of the ch. 2–4 interaction model. -/
abbrev Msg : Type := List Bool

/-- The embedded party **on its turn**, with `k` moves left in the protocol (its own included)
and received history `M`: it sends `next M`; after its send, `k − 1` moves are left, and it waits.
With no moves left it returns `next M`. -/
def turnParty (next : List Msg → Msg) : ℕ → List Msg → Party Msg Msg Msg
  | 0, M => .pure (next M)
  | k + 1, M => .query (.inl ()) (next M) fun
      | none => .pure (next M)
      | some y => match k with
        | 0 => .pure (next M)
        | k' + 1 => turnParty next k' (M ++ [y])

/-- With no moves left, the embedded party returns `next M`: `turnParty next 0 M = pure (next M)`.
-/
theorem turnParty_zero (next : List Msg → Msg) (M : List Msg) :
    turnParty next 0 M = .pure (next M) :=
  rfl

/-- The embedded party **while waiting**, with `k` moves left (the other party's next one
included) and received history `M`. On the other party's message `y` it takes its turn with
`k − 1` moves left; on `none` (the other party has returned) it returns `next M`. -/
def waitParty (next : List Msg → Msg) (k : ℕ) (M : List Msg) : Option Msg → Party Msg Msg Msg
  | none => .pure (next M)
  | some y => match k with
    | 0 => .pure (next M)
    | k' + 1 => turnParty next k' (M ++ [y])

/-- Waiting, on `none` (the other party has returned), the embedded party returns `next M`. -/
theorem waitParty_none (next : List Msg → Msg) (k : ℕ) (M : List Msg) :
    waitParty next k M none = .pure (next M) :=
  rfl

/-- Waiting with no moves left, a reply off schedule is ignored and the party returns `next M`. -/
theorem waitParty_some_zero (next : List Msg → Msg) (M : List Msg) (y : Msg) :
    waitParty next 0 M (some y) = .pure (next M) :=
  rfl

/-- Waiting with `k + 1` moves left, on the reply `y` the party appends it and takes its turn with
`k` moves left: `waitParty next (k + 1) M (some y) = turnParty next k (M ++ [y])`. -/
theorem waitParty_some_succ (next : List Msg → Msg) (k : ℕ) (M : List Msg) (y : Msg) :
    waitParty next (k + 1) M (some y) = turnParty next k (M ++ [y]) :=
  rfl

/-- On its turn with `k + 1` moves left, the embedded party sends `next M` and then waits with
`k` moves left. -/
theorem turnParty_succ (next : List Msg → Msg) (k : ℕ) (M : List Msg) :
    turnParty next (k + 1) M = .query (.inl ()) (next M) (waitParty next k M) := by
  rw [turnParty]
  congr 1

/-- **D8's alternation from a state:** the received histories of `F` and of `G` after `k` more
moves from `(MF, MG)`, with `F` to move. `F` sends `nF MF`, which `G` receives; then `G` moves. -/
def alt (nF nG : List Msg → Msg) : ℕ → List Msg → List Msg → List Msg × List Msg
  | 0, MF, MG => (MF, MG)
  | k + 1, MF, MG => (alt nG nF k (MG ++ [nF MF]) MF).swap

/-- With no moves left, the histories are unchanged: `alt nF nG 0 MF MG = (MF, MG)`. -/
theorem alt_zero (nF nG : List Msg → Msg) (MF MG : List Msg) : alt nF nG 0 MF MG = (MF, MG) :=
  rfl

/-- `alt`'s step at the front: `F` sends `nF MF` to `G`, then the roles are exchanged:
`alt nF nG (k + 1) MF MG = (alt nG nF k (MG ++ [nF MF]) MF).swap`. -/
theorem alt_succ (nF nG : List Msg → Msg) (k : ℕ) (MF MG : List Msg) :
    alt nF nG (k + 1) MF MG = (alt nG nF k (MG ++ [nF MF]) MF).swap :=
  rfl

/-- `alt`'s step at the back: after `k + 1` moves, the last move is `F`'s when `k` is even (its
message, computed on its history, is appended to `G`'s), and `G`'s when `k` is odd. This is D8's
`exec_succ` shape.

**Proof sketch.** Induction on `k`, generalizing over the two functions and the histories:
`alt`'s step exchanges the roles and the parity of the remaining moves together. -/
theorem alt_succ_last : ∀ (k : ℕ) (nF nG : List Msg → Msg) (MF MG : List Msg),
    alt nF nG (k + 1) MF MG =
      if k % 2 = 0 then ((alt nF nG k MF MG).1, (alt nF nG k MF MG).2 ++ [nF (alt nF nG k MF MG).1])
      else ((alt nF nG k MF MG).1 ++ [nG (alt nF nG k MF MG).2], (alt nF nG k MF MG).2) := by
  intro k
  induction k with
  | zero => intro nF nG MF MG; rfl
  | succ k ih =>
    intro nF nG MF MG
    rw [alt, ih nG nF (MG ++ [nF MF]) MF]
    simp only [alt]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have h' : ¬ (k + 1) % 2 = 0 := by omega
      simp [h, h']
    · have h' : (k + 1) % 2 = 0 := by omega
      simp [h, h']

/-- **Embedded executions are D8's:** with fuel `k`, the number of moves, the execution of `F` on
its turn against `G` waiting returns both outputs, `nF` and `nG` on the final histories of
`alt`.

**Proof sketch.** Induction on `k`, generalizing over the two next-message functions and the
histories.
- With no moves, `F` returns `nF MF`, and `G` is closed with `none` and returns `nG MG`.
- With `k + 1` moves, `exec_succ` and `turnParty_succ` send `nF MF` to `G`, which takes its turn
  with `k` moves left (`waitParty`), against `F` waiting with `k` moves left. The induction
  hypothesis with the roles exchanged, and `ExecOutcome.swap`, give the outputs; `alt`'s step is
  the same exchange. -/
theorem exec_turnParty : ∀ (k : ℕ) (nF nG : List Msg → Msg) (MF MG : List Msg),
    Party.exec k (turnParty nF k MF) (waitParty nG k MG) =
      .pure (.done (nF (alt nF nG k MF MG).1) (nG (alt nF nG k MF MG).2)) := by
  intro k
  induction k with
  | zero =>
    intro nF nG MF MG
    simp only [turnParty_zero, Party.exec_zero, Party.step_pure, OracleComp.pure_bind,
      Sum.elim_inl, Party.endWith_eq, waitParty_none, Party.close_pure, Option.elim_some,
      alt_zero]
  | succ k ih =>
    intro nF nG MF MG
    simp only [turnParty_succ, Party.exec_succ, Party.step_send, OracleComp.pure_bind,
      Sum.elim_inr, waitParty_some_succ, ih, ExecOutcome.swap_done, alt_succ, Prod.fst_swap,
      Prod.snd_swap]

/-- **D8's `exec` is `alt`:** after `k` moves from the empty histories, the messages received by
`P` and by `V` are `alt`'s, with the first mover chosen by `vFirst`.

**Proof sketch.** Generalize to `j + k` moves: D8's state after `j` moves, continued by `alt`
for `k` more with the mover at position `j` (`moverIsV`), is D8's state after `j + k` moves.
Induct on `k`; the parity of `j` decides who moves, and `exec_succ` (D8's) appends the message
to the other party's list exactly as `alt`'s step does. -/
theorem exec_eq_alt (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    exec P V vFirst x zP zV rP rV k =
      if vFirst then (alt (V.next x zV rV) (P.next x zP rP) k [] []).swap
      else alt (P.next x zP rP) (V.next x zV rV) k [] [] := by
  induction k with
  | zero =>
    cases vFirst <;>
      simp only [exec_zero, alt_zero, Bool.false_eq_true, ↓reduceIte, Prod.swap_prod_mk]
  | succ k ih =>
    rw [exec_succ, ih]
    cases vFirst <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> rw [alt_succ_last] <;>
      rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [moverIsV_true, moverIsV_false, h]

/-- **A protocol's embedded execution returns D8's outputs:** for fixed tapes, running the first
mover's embedding on its turn against the other's waiting embedding, with fuel the number of
messages, returns the prover's and the verifier's D8 outputs (`Protocol.outP`,
`Protocol.outV`), in the first mover's order.

**Proof sketch.** `exec_turnParty` with `k = π.rounds.eval |x|` and the next-message functions of
the two strategies, then `exec_eq_alt` with `π.transcriptWith`'s unfolding; `outP` and `outV`
are the next-message functions on the final histories. -/
theorem exec_strategies (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    Party.exec (π.rounds.eval x.length)
        (turnParty (if π.verifierFirst then π.V.next x z (List.ofFn r.2)
          else π.P.next x y (List.ofFn r.1)) (π.rounds.eval x.length) [])
        (waitParty (if π.verifierFirst then π.P.next x y (List.ofFn r.1)
          else π.V.next x z (List.ofFn r.2)) (π.rounds.eval x.length) []) =
      .pure (if π.verifierFirst then .done (π.outV π.P x y z r) (π.outP x y z r)
        else .done (π.outP x y z r) (π.outV π.P x y z r)) := by
  have hT := exec_eq_alt π.P π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2)
    (π.rounds.eval x.length)
  simp only [Protocol.outP_eq, Protocol.outV_eq, Protocol.transcriptWith_eq]
  cases hv : π.verifierFirst
  · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hT ⊢
    rw [exec_turnParty, hT]
  · simp only [hv, ↓reduceIte] at hT ⊢
    rw [exec_turnParty, hT, Prod.fst_swap, Prod.snd_swap]

end TCSlib.Cryptography.Games.Bridge
