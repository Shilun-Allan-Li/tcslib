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
message, the other party resumes with that message and runs until it replies, and so on, for at
most `fuel` messages.

**When a party returns.** [PS10, §4.4] ends the protocol when the active machine halts, and gives
a machine an output only on halting, so the waiting party has none. Yet Definitions 116.1 and
155.1 use both parties' outputs. Following the ch. 2–4 layer's foundation decision D8
(`TCSlib.Cryptography.ZeroKnowledge.Interaction`), both parties have outputs: the waiting party is
activated **once more**. Its pending send is answered `none` ("the other party has finished"), it
may draw coins, and it must then return without sending. A send after the end is reported
(`ExecOutcome.sentAfterEnd`), never hidden.

**A broader model than D8's.** The executor is a coroutine model that contains D8's. It is broader
in two respects. A party may return early (D8 fixes the number of messages). And a party's output
is a separate return value (in D8 it is the next-message function on the complete history, so the
last sender's output equals its last message). D8's executions are those of *embedded strategies*:
each samples its whole tape first, sends `next` on its scheduled turns, and returns `next` on its
complete history. Agreement with D8 is claimed only for that class (bridge B4, S2b).

**Traces.** `Party.execT` returns, beside the outcome, each party's received messages (the second
mover's first message first) and the coin draws it executed (`Party.Obs`). Its outcome is that of
`Party.exec` (`Party.execT_outcome`). A [PS10, §4.4] view `(x, z, r, M)` contains the whole random
tape `r`, including bits never read. It is recovered from the trace only for parties that sample
their whole tape first, as an embedded strategy does. Inputs and auxiliary inputs are Lean
parameters of the party. A party's own oracle log would miss the second mover's first message,
which reaches it as an argument.

The ch. 2–4 layer's strategies (`TCSlib.Cryptography.Strategy`, `TCSlib.Cryptography.exec`) remain
the definitions of interaction for IP, ZK and two-party computation (ruling of 2026-11-05). This
executor is the calculus in which their properties are proved, through B4.

## Main definitions

* `Games.exchangeSpec Out In`: the message-exchange oracle (send an `Out`, receive an `In` or
  `none`).
* `Games.Party Out In α`: a party sending `Out`, receiving `In`, drawing its own coins and returning
  an `α`.
* `Games.ExecOutcome`: both outputs, out of fuel, or a send after the end.
* `Games.Party.step`, `Games.Party.close`: run a party to its next send or return; close a party
  whose counterpart has returned.
* `Games.Party.exec fuel A B`: execute a protocol in which `A` moves first, with at most `fuel`
  messages.
* `Games.Party.Obs`, `Games.Party.execT`: the traced execution, recording each party's received
  messages and coins.

## Main results

* `Games.Party.exec_zero`, `Party.exec_succ`: the execution equations.
* `Games.Party.execT_outcome`: the traced execution has the outcome of the execution.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines, executions, views), Definitions 116.1 and 155.1.
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

/-- The **message-exchange oracle**: the query is the message sent, and the answer is the other
party's next message, or `none` if the other party has returned. [PS10, §4.4] -/
abbrev exchangeSpec (Out In : Type) : OracleSpec Unit := ⟨fun _ => Out, fun _ => Option In⟩

/-- A **party** of a two-party protocol: sends messages of type `Out`, receives messages of type
`In`, draws its own coins, and returns an `α`. [PS10, §4.4] -/
abbrev Party (Out In α : Type) : Type := OracleComp ((exchangeSpec Out In).add unifSpec) α

/-- The **outcome of an execution**: both outputs; the message budget ran out; or a party sent a
message after its counterpart had returned. -/
inductive ExecOutcome (α β : Type) : Type where
  /-- Both parties returned: the first mover's output and the second mover's. -/
  | done (a : α) (b : β)
  /-- The message budget ran out before both parties returned. -/
  | outOfFuel
  /-- A party sent a message after its counterpart had returned. -/
  | sentAfterEnd

/-- Exchange the roles in an outcome. -/
def ExecOutcome.swap {α β : Type} : ExecOutcome α β → ExecOutcome β α
  | .done a b => .done b a
  | .outOfFuel => .outOfFuel
  | .sentAfterEnd => .sentAfterEnd

namespace Party

variable {Out In α β : Type}

/-- Run a party until it returns or sends a message, passing its coin draws through. The result is
either its output, or the message it sends together with how it continues on the reply. -/
def step : Party Out In α → ProbComp (α ⊕ (Out × (Option In → Party Out In α)))
  | .pure a => .pure (.inl a)
  | .query (.inl ()) m k => .pure (.inr (m, k))
  | .query (.inr j) x k => .query j x (fun y => step (k y))

/-- **Close** a party whose counterpart has returned (its pending send already answered `none`):
it may still draw coins, and returns `some` of its output, or `none` if it sends a message. -/
def close : Party Out In α → ProbComp (Option α)
  | .pure a => .pure (some a)
  | .query (.inl ()) _ _ => .pure none
  | .query (.inr j) x k => .query j x (fun y => close (k y))

/-- The end of an execution in which the active party returned `a`: the waiting party `B` is
activated once more, with `none`, and closed. -/
def endWith {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    ProbComp (ExecOutcome α β) :=
  (close (B none)).bind fun ob => .pure (Option.elim ob .sentAfterEnd (ExecOutcome.done a))

/-- **Execution** of a two-party protocol with at most `fuel` messages. `A` moves first, and `B`
waits for `A`'s first message. After each message the roles swap. A return costs no fuel; when the
active party returns, the waiting party is activated once more and closed (`endWith`).

**Deviation from [PS10, §4.4]:** the source ends the protocol when the active machine halts and
defines outputs only on halting, so the waiting party would have none, while Definitions 116.1
and 155.1 use both outputs. Following the ch. 2–4 layer's D8, the waiting party is activated once
more; it may draw coins, but a send is reported as `sentAfterEnd`.

**Relation to D8.** This executor is broader than D8 in two respects. A party may return early
(D8 fixes the number of messages). And a party's output is a separate return value, computed after
its last activation and possibly after fresh coins on closure. In D8 a party's output is its
next-message function on its complete history, so the last sender's output equals its last
message (`Protocol.outV_eq_getLast_of_moverIsV`). D8's executions are the executions of embedded
strategies (each samples its whole tape first, sends `next` on its scheduled turns, and returns
`next` on its complete history). Agreement with D8 is claimed only for that class (bridge B4). -/
def exec : ℕ → ∀ {M₁ M₂ α β : Type},
    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) → ProbComp (ExecOutcome α β)
  | 0, _, _, _, _, A, B =>
    (step A).bind (Sum.elim (fun a => endWith a B) (fun _ => .pure .outOfFuel))
  | fuel + 1, _, _, _, _, A, B =>
    (step A).bind (Sum.elim (fun a => endWith a B)
      (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure r.swap))

/-- With no fuel, the first mover runs until it returns or tries to send. If it returns, the
waiting party is closed (`endWith`): activated with `none`, it may draw coins, and the outcome is
`done` if it returns and `sentAfterEnd` if it sends. If the first mover tries to send, the outcome
is `outOfFuel` and the waiting party never runs. -/
@[simp] theorem exec_zero {M₁ M₂ : Type} (A : Party M₁ M₂ α) (B : Option M₁ → Party M₂ M₁ β) :
    exec 0 A B = (step A).bind (Sum.elim (fun a => endWith a B) (fun _ => .pure .outOfFuel)) :=
  rfl

/-- One message of the execution: `A` runs until it returns (then `B` is closed) or sends `m`
(then `B` resumes with `m` as the first mover, against `A`'s continuation). -/
theorem exec_succ {M₁ M₂ : Type} (fuel : ℕ) (A : Party M₁ M₂ α)
    (B : Option M₁ → Party M₂ M₁ β) :
    exec (fuel + 1) A B =
      (step A).bind (Sum.elim (fun a => endWith a B)
        (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure r.swap)) :=
  rfl

/-! ### Sanity checks: fuel counts messages; a send after the end is reported -/

example (a b : Bool) :
    exec 0 (M₁ := Unit) (M₂ := Unit) (.pure a) (fun _ => .pure b) = .pure (.done a b) := rfl

example (m : Unit) (a b : Bool) :
    exec 1 (M₂ := Unit) (.query (.inl ()) m fun _ => .pure a) (fun _ => .pure b) =
      .pure (.done a b) := rfl

example (m : Unit) (a b : Bool) :
    exec 1 (M₁ := Unit) (.pure a) (fun _ => .query (.inl ()) m fun _ => .pure b) =
      .pure .sentAfterEnd := rfl

/-! ### The traced execution -/

/-- What one party **observes** during an execution: the messages delivered to it, in order, and
the coins it drew, each as a sampling oracle `m` with its answer in `Fin (m + 1)`. -/
structure Obs (In : Type) : Type where
  /-- The messages delivered to the party, in order. -/
  received : List In
  /-- The party's coin draws, in order. -/
  coins : List (Σ m : ℕ, Fin (m + 1))

/-- `step`, also returning the coins drawn along the way. -/
def stepT : Party Out In α →
    ProbComp ((α ⊕ (Out × (Option In → Party Out In α))) × List (Σ m : ℕ, Fin (m + 1)))
  | .pure a => .pure (.inl a, [])
  | .query (.inl ()) m k => .pure (.inr (m, k), [])
  | .query (.inr j) x k => .query j x fun y =>
      (stepT (k y)).bind fun p => .pure (p.1, ⟨j, y⟩ :: p.2)

/-- `close`, also returning the coins drawn along the way. -/
def closeT : Party Out In α → ProbComp (Option α × List (Σ m : ℕ, Fin (m + 1)))
  | .pure a => .pure (some a, [])
  | .query (.inl ()) _ _ => .pure (none, [])
  | .query (.inr j) x k => .query j x fun y =>
      (closeT (k y)).bind fun p => .pure (p.1, ⟨j, y⟩ :: p.2)

/-- The traced end of an execution: `endWith`, also returning the waiting party's coins. -/
def endWithT {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    ProbComp (ExecOutcome α β × List (Σ m : ℕ, Fin (m + 1))) :=
  (closeT (B none)).bind fun p => .pure (Option.elim p.1 .sentAfterEnd (ExecOutcome.done a), p.2)

/-- The **traced execution**: `exec`, also returning what each party observed. The first component
of the result is the outcome, the second the first mover's observations, and the third the second
mover's. When the active party sends `m`, `m` is the first message the other party receives in the
rest of the run. [PS10, §4.4] (the received messages of a view; its random tape for parties that
sample it first) -/
def execT : ℕ → ∀ {M₁ M₂ α β : Type},
    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) →
      ProbComp (ExecOutcome α β × Obs M₂ × Obs M₁)
  | 0, _, _, _, _, A, B =>
    (stepT A).bind fun p => Sum.elim
      (fun a => (endWithT a B).bind fun q => .pure (q.1, ⟨[], p.2⟩, ⟨[], q.2⟩))
      (fun _ => .pure (.outOfFuel, ⟨[], p.2⟩, ⟨[], []⟩)) p.1
  | fuel + 1, _, _, _, _, A, B =>
    (stepT A).bind fun p => Sum.elim
      (fun a => (endWithT a B).bind fun q => .pure (q.1, ⟨[], p.2⟩, ⟨[], q.2⟩))
      (fun mk => (execT fuel (B (some mk.1)) mk.2).bind fun r =>
        .pure (r.1.swap, ⟨r.2.2.received, p.2 ++ r.2.2.coins⟩,
          ⟨mk.1 :: r.2.1.received, r.2.1.coins⟩)) p.1

/-- An ended execution never reports a spent budget: the outcome of `endWithT` is `done` or
`sentAfterEnd`. -/
theorem endWithT_ne_outOfFuel {M₁ M₂ : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    (endWithT a B).AllOutputs fun q => q.1 ≠ .outOfFuel := by
  refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun p _ => ?_
  show Option.elim p.1 ExecOutcome.sentAfterEnd (ExecOutcome.done a) ≠ .outOfFuel
  cases p.1 <;> simp [Option.elim]

/-- **Trace invariants** (gate 02 round 2, note 5): on every possible run of
`execT fuel A B`, write `M_A` and `M_B` for the messages delivered to the first and the second
mover. Then `|M_A| + |M_B| ≤ fuel`; the second mover has received as many messages as the first
or one more (it receives first); and a spent budget means exactly `fuel` messages were delivered.

**Proof sketch.** Induction on `fuel`, generalizing the parties and their types. A return or a
blocked send delivers nothing (both lists are empty), and `endWithT` never reports a spent budget.
A delivered message adds one message to the receiver, and the recursive run, with the roles
exchanged, satisfies the invariants with `fuel − 1`; exchanging back keeps them, since its first
mover is the original second mover. -/
theorem execT_trace : ∀ (fuel : ℕ) {M₁ M₂ α β : Type} (A : Party M₁ M₂ α)
    (B : Option M₁ → Party M₂ M₁ β),
    (execT fuel A B).AllOutputs fun r =>
      r.2.1.received.length + r.2.2.received.length ≤ fuel ∧
      (r.2.2.received.length = r.2.1.received.length ∨
        r.2.2.received.length = r.2.1.received.length + 1) ∧
      (r.1 = .outOfFuel → r.2.1.received.length + r.2.2.received.length = fuel)
  | 0, _, _, _, _, A, B => by
    refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun p _ => ?_
    rcases p with ⟨a | mk, cs⟩
    · exact OracleComp.AllOutputs.bind (endWithT_ne_outOfFuel a B) fun q hq =>
        ⟨by simp, by simp, fun h => absurd h hq⟩
    · exact ⟨by simp, by simp, fun _ => by simp⟩
  | fuel + 1, _, _, _, _, A, B => by
    refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun p _ => ?_
    rcases p with ⟨a | mk, cs⟩
    · exact OracleComp.AllOutputs.bind (endWithT_ne_outOfFuel a B) fun q hq =>
        ⟨by simp, by simp, fun h => absurd h hq⟩
    · refine OracleComp.AllOutputs.bind (execT_trace fuel (B (some mk.1)) mk.2) fun r hr => ?_
      obtain ⟨h1, h2, h3⟩ := hr
      refine ⟨?_, ?_, fun h => ?_⟩
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
      · have : r.1 = .outOfFuel := by
          cases hr1 : r.1 <;> simp_all [ExecOutcome.swap]
        have := h3 this
        simp only [List.length_cons]; omega

/-- `stepT` projects to `step`. -/
theorem stepT_fst (A : Party Out In α) : (stepT A).bind (fun p => .pure p.1) = step A := by
  induction A with
  | pure a => rfl
  | query i x k ih =>
    cases i with
    | inl u => cases u; rfl
    | inr j =>
      simp only [stepT, step, OracleComp.query_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
      congr 1
      funext y
      exact ih y

/-- `closeT` projects to `close`. -/
theorem closeT_fst (A : Party Out In α) : (closeT A).bind (fun p => .pure p.1) = close A := by
  induction A with
  | pure a => rfl
  | query i x k ih =>
    cases i with
    | inl u => cases u; rfl
    | inr j =>
      simp only [closeT, close, OracleComp.query_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
      congr 1
      funext y
      exact ih y

/-- `endWithT` projects to `endWith`. -/
theorem endWithT_fst {M₁ M₂ : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    (endWithT a B).bind (fun q => .pure q.1) = endWith a B := by
  simp only [endWithT, endWith, OracleComp.bind_assoc, OracleComp.pure_bind]
  rw [← closeT_fst (B none), OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind]

/-- **The traced execution has the execution's outcome.**

**Proof sketch.** Induction on the fuel, generalizing the parties and their types. Each level of
`execT` runs `stepT`, which projects to `step` (`stepT_fst`); the branch on the first component
then matches `exec`'s, with `endWithT` projecting to `endWith` and the recursive call to the
recursive call. -/
theorem execT_outcome : ∀ (fuel : ℕ) {M₁ M₂ α β : Type} (A : Party M₁ M₂ α)
    (B : Option M₁ → Party M₂ M₁ β),
    (execT fuel A B).bind (fun r => .pure r.1) = exec fuel A B
  | 0, _, _, _, _, A, B => by
    simp only [execT, exec, OracleComp.bind_assoc]
    rw [← stepT_fst A, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    congr 1
    funext p
    rcases p with ⟨_ | _, c⟩
    · simp only [Sum.elim_inl, OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [← endWithT_fst]
    · rfl
  | fuel + 1, _, _, _, _, A, B => by
    simp only [execT, exec, OracleComp.bind_assoc]
    rw [← stepT_fst A, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    congr 1
    funext p
    rcases p with ⟨_ | mk, c⟩
    · simp only [Sum.elim_inl, OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [← endWithT_fst]
    · simp only [Sum.elim_inr, OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [← execT_outcome fuel (B (some mk.1)) mk.2, OracleComp.bind_assoc]
      simp only [OracleComp.pure_bind]

end Party

end TCSlib.Cryptography.Games
