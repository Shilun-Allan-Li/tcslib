/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Two-party protocols as oracle computations

A party of a two-party protocol is an oracle computation with two kinds of oracles: the message
exchange (send a message, receive the other party's next message) and its own coins. Running the
protocol interleaves the two parties as coroutines: the active party runs until it sends a
message, the other party resumes with that message and runs until it replies, and so on. When a
party returns its output, the other party's pending send is answered `none` ("the other party has
finished"), so it too can finish.

This is the same framework as security games: a party's view (its coins and the messages it
received) is the log of its own oracle answers, and simulation-based security compares two
`ProbComp`s with `advantage`. The bridge to the next-message strategies of the ch. 2–4 layer
(`TCSlib.Cryptography.Strategy`, `TCSlib.Cryptography.exec`) is part of the S2b layer.

## Main definitions

* `Games.exchangeSpec Out In`: the message-exchange oracle (send an `Out`, receive an `In` or
  `none`).
* `Games.Party Out In α`: a party sending `Out`, receiving `In`, drawing its own coins and returning
  an `α`.
* `Games.Party.step`: run a party until it returns or sends a message.
* `Games.Party.finish`: finish a party whose counterpart has returned.
* `Games.Party.exec fuel A B`: execute a protocol in which `A` moves first, with at most `fuel`
  messages.

## Main results

* `Games.Party.exec_zero`, `Party.exec_succ`: the execution equations.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines, executions, views) and §6.2 (two-party secure computation).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

/-- The **message-exchange oracle**: the query is the message sent, and the answer is the other
party's next message, or `none` if the other party has returned. [PS10, §4.4] -/
abbrev exchangeSpec (Out In : Type) : OracleSpec Unit := ⟨fun _ => Out, fun _ => Option In⟩

/-- A **party** of a two-party protocol: sends messages of type `Out`, receives messages of type
`In`, draws its own coins, and returns an `α`. [PS10, §4.4] -/
abbrev Party (Out In α : Type) : Type := OracleComp ((exchangeSpec Out In).add unifSpec) α

namespace Party

variable {Out In α β : Type}

/-- Run a party until it returns or sends a message, passing its coin draws through. The result is
either its output, or the message it sends together with how it continues on the reply. -/
def step : Party Out In α → ProbComp (α ⊕ (Out × (Option In → Party Out In α)))
  | .pure a => .pure (.inl a)
  | .query (.inl ()) m k => .pure (.inr (m, k))
  | .query (.inr j) x k => .query j x (fun y => step (k y))

/-- Finish a party whose counterpart has returned: every further send is answered `none`. -/
def finish : Party Out In α → ProbComp α
  | .pure a => .pure a
  | .query (.inl ()) _ k => finish (k none)
  | .query (.inr j) x k => .query j x (fun y => finish (k y))

/-- **Execution** of a two-party protocol with at most `fuel` messages. `A` moves first, and `B`
waits for `A`'s first message (`none` if `A` returns at once). After each message the roles swap.
The result is both outputs, or `none` if the fuel runs out first. [PS10, §4.4] -/
def exec : ℕ → ∀ {M₁ M₂ α β : Type},
    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) → ProbComp (Option (α × β))
  | 0, _, _, _, _, _, _ => .pure none
  | fuel + 1, _, _, _, _, A, B =>
    (step A).bind (Sum.elim
      (fun a => (finish (B none)).bind fun b => .pure (some (a, b)))
      (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure (r.map Prod.swap)))

/-- Without fuel, the execution stops at once. -/
@[simp] theorem exec_zero {M₁ M₂ : Type} (A : Party M₁ M₂ α) (B : Option M₁ → Party M₂ M₁ β) :
    exec 0 A B = .pure none := rfl

/-- One move of the execution: `A` runs until it returns (then `B` finishes) or sends `m` (then
`B` resumes with `m` as the first mover, against `A`'s continuation). -/
theorem exec_succ {M₁ M₂ : Type} (fuel : ℕ) (A : Party M₁ M₂ α)
    (B : Option M₁ → Party M₂ M₁ β) :
    exec (fuel + 1) A B =
      (step A).bind (Sum.elim
        (fun a => (finish (B none)).bind fun b => .pure (some (a, b)))
        (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure (r.map Prod.swap))) :=
  rfl

end Party

end TCSlib.Cryptography.Games
