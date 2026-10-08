/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.OracleFinite
import TCSlib.Complexity.TuringMachine.Nondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic oracle Turing machines

[AB09, Definition 3.4] closes with "Nondeterministic oracle TMs are defined
similarly." This module is that definition: the binary-choice nondeterministic
machine of `TCSlib.Complexity.TuringMachine.Nondeterministic` equipped with the
query tape and query/answer states of `TCSlib.Complexity.TuringMachine.Oracle`.
It exists for `Complexity.NPOracle` ([AB09, Definition 3.5]) and for the
relativization theorem ([AB09, Theorem 3.7], phase P3.2).

## Design

* **The oracle answer consumes a choice bit but ignores it.** A step in state
  `qQuery` resolves the query exactly as `Turing.OracleTM.step` does — move to
  `qYes`/`qNo` according to membership of the current query string, tapes and
  heads unchanged — under **either** choice bit. Choice words therefore have one
  bit per step uniformly, keeping the choice-word run algebra (and the
  certificate reading of choice words, [AB09, §2.1.2]) identical to the plain
  NDTM's. The alternative (query steps consume no bit) would make branch length
  input-dependent in a way nothing downstream wants.
* Everything else mirrors the two parents: `Symbol`/`State` unconstrained at the
  raw layer, the bundled finite layer (`Turing.FinOracleNDTM`, in
  `TCSlib.Complexity.TuringMachine.OracleFinite`'s style) carries
  `Fintype`/`DecidableEq` as data and well-formedness as a field.
* The three-state distinctness discipline is `Turing.OracleNDTM.WellFormed`,
  verbatim the deterministic `Turing.OracleTM.WellFormed` rationale
  (`audits/phase1-findings.md`, finding 2).

## Main definitions

* `Turing.OracleNDTM` — the binary-choice oracle machine. [AB09, Def 3.4, last
  sentence]
* `Turing.OracleNDTM.WellFormed` — pairwise-distinct special states.
* `Turing.OracleNDTM.stepWith`, `Turing.OracleNDTM.runWith` — one step under a
  choice bit and an oracle; the run under a choice word.
* `Turing.OracleNDTM.HaltsWithin`, `Turing.FinOracleNDTM.AcceptsWithin`,
  `Turing.FinOracleNDTM.DecidesInTime` — all-branch halting, existential
  acceptance, and decision, mirroring the `NTIME` layer.
* `Turing.FinOracleNDTM` — the bundled finite, well-formed layer.
* `Turing.OracleTM.toOracleNDTM`, `Turing.FinOracleTM.toFinOracleNDTM` — a
  deterministic oracle machine as one that ignores its choices.

## Main results

* `Turing.OracleNDTM.runWith_append`, `Turing.OracleNDTM.runWith_of_halt` — the
  choice-word run algebra (proved; pure unfoldings mirroring the plain NDTM's,
  declared part of the audited surface per `workflow.md` §2).
* `Turing.OracleNDTM.HaltsWithin.mono` — all-branch halting is monotone (proved,
  same unfolding argument as `Turing.NDTM.HaltsWithin.mono`).
* `Turing.OracleTM.toOracleNDTM_runWith` — the embedded deterministic oracle
  machine ignores its choices (sorried; the lockstep obligation of phase P3.1).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Definitions 3.4-3.5; §2.1.2.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- A binary-choice nondeterministic oracle Turing machine: two total transition
functions on `k + 1` work tapes (the last being the query tape, as in
`Turing.OracleTM`), an initial state, and the designated `qQuery`/`qYes`/`qNo`
states. [AB09, Definition 3.4: "Nondeterministic oracle TMs are defined
similarly"] -/
structure OracleNDTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- entering this state submits the query tape's contents to the oracle -/
  qQuery : State
  /-- the state the oracle answer step moves to on a positive answer -/
  qYes : State
  /-- the state the oracle answer step moves to on a negative answer -/
  qNo : State
  /-- the two transition functions, indexed by the nondeterministic choice bit;
  consulted in every state except `qQuery` -/
  tr (choice : Bool) (q : State) (input : Option Symbol)
    (work : Fin (k + 1) → Option Symbol) : Action (k + 1) Symbol State

namespace OracleNDTM

variable {N : OracleNDTM k Symbol State}

/-- Well-formedness: the query state and the two answer states are pairwise
distinct — verbatim the `Turing.OracleTM.WellFormed` discipline and rationale
(`q₀ = qQuery` stays deliberately allowed). -/
structure WellFormed (N : OracleNDTM k Symbol State) : Prop where
  /-- the query state is not the positive-answer state -/
  qQuery_ne_qYes : N.qQuery ≠ N.qYes
  /-- the query state is not the negative-answer state -/
  qQuery_ne_qNo : N.qQuery ≠ N.qNo
  /-- the two answer states are distinct -/
  qYes_ne_qNo : N.qYes ≠ N.qNo

open Classical in
/-- One step under the choice bit `b` and the oracle `O`: in state `qQuery` the
machine resolves the query exactly as the deterministic oracle step does — the
choice bit is consumed but ignored — and in every other live state it applies the
action selected by `tr b`. Halting is absorbing under every choice. -/
noncomputable def stepWith (N : OracleNDTM k Symbol State) (O : Language Symbol)
    (b : Bool) (cfg : Cfg (k + 1) Symbol State input) : Cfg (k + 1) Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q =>
    if q = N.qQuery then
      { cfg with state := some (if OracleTM.queryString cfg ∈ O then N.qYes else N.qNo) }
    else
      (N.tr b q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The initial configuration: all `k + 1` work tapes (including the query tape)
blank, input head on the first symbol. -/
@[simp]
def initCfg (N : OracleNDTM k Symbol State) (input : List Symbol) :
    Cfg (k + 1) Symbol State input :=
  Cfg.init N.q₀ input

/-- The configuration reached from `cfg` by running under the choice word `w` with
oracle `O`, one choice bit per step, consumed left to right. -/
noncomputable def runWith (N : OracleNDTM k Symbol State) (O : Language Symbol) :
    List Bool → Cfg (k + 1) Symbol State input → Cfg (k + 1) Symbol State input
  | [], cfg => cfg
  | b :: w, cfg => N.runWith O w (N.stepWith O b cfg)

/-- The empty choice word runs zero steps. -/
@[simp]
lemma runWith_nil (O : Language Symbol) {cfg : Cfg (k + 1) Symbol State input} :
    N.runWith O [] cfg = cfg := rfl

/-- Consuming one choice bit is one step. -/
lemma runWith_cons (O : Language Symbol) {b : Bool} {w : List Bool}
    {cfg : Cfg (k + 1) Symbol State input} :
    N.runWith O (b :: w) cfg = N.runWith O w (N.stepWith O b cfg) := rfl

/-- Running under `w ++ w'` is running under `w`, then under `w'` from the reached
configuration — the oracle counterpart of `Turing.NDTM.runWith_append`. -/
lemma runWith_append (O : Language Symbol) (w w' : List Bool)
    (cfg : Cfg (k + 1) Symbol State input) :
    N.runWith O (w ++ w') cfg = N.runWith O w' (N.runWith O w cfg) := by
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih => rw [List.cons_append, runWith_cons, runWith_cons, ih]

/-- Stepping a halted configuration is the identity, under either choice and any
oracle. -/
@[simp]
lemma stepWith_of_halt (O : Language Symbol) {b : Bool}
    {cfg : Cfg (k + 1) Symbol State input} (h : cfg.state = none) :
    N.stepWith O b cfg = cfg := by
  unfold stepWith
  rw [h]

/-- Running from a halted configuration stays there, under every choice word. -/
@[simp]
lemma runWith_of_halt (O : Language Symbol) (cfg : Cfg (k + 1) Symbol State input)
    (h : cfg.state = none) {w : List Bool} : N.runWith O w cfg = cfg := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [runWith_cons, stepWith_of_halt O h]; exact ih

/-- The machine halts on `input` within `t` steps along **every** branch, relative
to the oracle `O` — [AB09]'s all-branch totality condition, rendered over choice
words of length exactly `t` exactly as in `Turing.NDTM.HaltsWithin`. -/
def HaltsWithin (N : OracleNDTM k Symbol State) (O : Language Symbol)
    (input : List Symbol) (t : ℕ) : Prop :=
  ∀ w : List Bool, w.length = t → (N.runWith O w (N.initCfg input)).state = none

/-- All-branch halting is monotone in the time bound.

**Proof sketch.** Identical to `Turing.NDTM.HaltsWithin.mono`: split `w` at `t`
(`List.take_append_drop`), the run under `w.take t` is halted by hypothesis,
`runWith_append` factors the run and `runWith_of_halt` absorbs the remainder. -/
theorem HaltsWithin.mono {N : OracleNDTM k Symbol State} {O : Language Symbol}
    {input : List Symbol} {t t' : ℕ} (h : N.HaltsWithin O input t) (hle : t ≤ t') :
    N.HaltsWithin O input t' := by
  intro w hw
  have hlen : (w.take t).length = t := List.length_take_of_le (hle.trans_eq hw.symm)
  have hhalt := h (w.take t) hlen
  have hrun := runWith_append (N := N) O (w.take t) (w.drop t) (N.initCfg input)
  rw [List.take_append_drop, runWith_of_halt O _ hhalt] at hrun
  rw [hrun]
  exact hhalt

end OracleNDTM

/-- A nondeterministic oracle machine bundled with a finite state type and the
well-formedness discipline, mirroring `Turing.FinOracleTM`: all nondeterministic
oracle complexity definitions (`Complexity.NPOracle`) are stated over this layer. -/
structure FinOracleNDTM (Symbol : Type) : Type 1 where
  /-- number of ordinary work tapes (the query tape is the extra one) -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible -/
  [decEqState : DecidableEq State]
  /-- the underlying nondeterministic oracle machine -/
  tm : OracleNDTM k Symbol State
  /-- the three special states are pairwise distinct -/
  wf : tm.WellFormed

namespace FinOracleNDTM

attribute [instance] FinOracleNDTM.fintypeState FinOracleNDTM.decEqState

/-- The machine `N`, with oracle `O`, *accepts* `x` within `t` steps: some choice
word of length `t` leaves it halted with output exactly `[true]` — mirroring
`Turing.FinNDTM.AcceptsWithin` (output-based acceptance, same deviation record). -/
def AcceptsWithin (N : FinOracleNDTM Bool) (O : Language Bool) (x : List Bool)
    (t : ℕ) : Prop :=
  ∃ w : List Bool, w.length = t ∧
    (N.tm.runWith O w (N.tm.initCfg x)).state = none ∧
    (N.tm.runWith O w (N.tm.initCfg x)).output = [true]

/-- Acceptance is monotone in the branch length.

**Proof sketch.** Pad the accepting word with `false`s; `runWith_append` and
`runWith_of_halt` absorb the padding, as in `Turing.FinNDTM.AcceptsWithin.mono`. -/
theorem AcceptsWithin.mono {N : FinOracleNDTM Bool} {O : Language Bool}
    {x : List Bool} {t t' : ℕ} (h : N.AcceptsWithin O x t) (hle : t ≤ t') :
    N.AcceptsWithin O x t' := by
  obtain ⟨w, hw, hhalt, hout⟩ := h
  refine ⟨w ++ List.replicate (t' - t) false, ?_, ?_⟩
  · rw [List.length_append, List.length_replicate, hw, Nat.add_sub_of_le hle]
  · rw [OracleNDTM.runWith_append, OracleNDTM.runWith_of_halt O _ hhalt]
    exact ⟨hhalt, hout⟩

/-- The machine `N`, with oracle `O`, decides `L` within time `T`: on every input,
every branch of length `T |x|` has halted, and `x ∈ L` exactly when some such
branch accepts — mirroring `Turing.FinNDTM.DecidesInTime`.
[AB09, Definition 3.5, nondeterministic half] -/
def DecidesInTime (N : FinOracleNDTM Bool) (O : Language Bool) (L : Language Bool)
    (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    N.tm.HaltsWithin O x (T x.length) ∧ (x ∈ L ↔ N.AcceptsWithin O x (T x.length))

end FinOracleNDTM

/-- A deterministic oracle machine as a nondeterministic one whose two transition
functions coincide — the oracle counterpart of `Turing.MultiTapeTM.toNDTM`, with
the special states carried over verbatim. -/
def OracleTM.toOracleNDTM (M : OracleTM k Symbol State) : OracleNDTM k Symbol State :=
  ⟨M.q₀, M.qQuery, M.qYes, M.qNo, fun _ => M.tr⟩

/-- The embedding preserves well-formedness (the special states are unchanged). -/
theorem OracleTM.toOracleNDTM_wellFormed {M : OracleTM k Symbol State}
    (h : M.WellFormed) : M.toOracleNDTM.WellFormed :=
  ⟨h.qQuery_ne_qYes, h.qQuery_ne_qNo, h.qYes_ne_qNo⟩

/-- The embedded deterministic oracle machine ignores its choices: running
`toOracleNDTM` under any choice word `w` with oracle `O` is running the original
machine for `|w|` steps with the same oracle — the oracle counterpart of
`Turing.MultiTapeTM.toNDTM_runWith`, and the engine of
`Complexity.POracle_subset_NPOracle`.

**Proof sketch.** Induction on `w` generalizing the configuration. One
`Turing.OracleNDTM.stepWith` of `toOracleNDTM` and one `Turing.OracleTM.step`
are the same match on the state: halted branches are both the identity; in state
`qQuery` both resolve the query through `Turing.OracleTM.queryString` with tapes
unchanged (the choice bit is ignored by construction); in any other live state
both apply the action `M.tr q …`, since `toOracleNDTM.tr b = M.tr` for either
`b`. The cons case is `Turing.OracleNDTM.runWith_cons` against the successor
unfolding of `Turing.OracleTM.runFrom` (`Function.iterate_succ_apply`). -/
theorem OracleTM.toOracleNDTM_runWith (M : OracleTM k Symbol State)
    (O : Language Symbol) {input : List Symbol} (w : List Bool)
    (cfg : Cfg (k + 1) Symbol State input) :
    M.toOracleNDTM.runWith O w cfg = M.runFrom O cfg w.length := by
  sorry

/-- A bundled deterministic oracle machine as a bundled nondeterministic one, with
the same tapes, state type, and special states. -/
def FinOracleTM.toFinOracleNDTM {Symbol : Type} (M : FinOracleTM Symbol) :
    FinOracleNDTM Symbol :=
  ⟨M.k, M.State, M.tm.toOracleNDTM, OracleTM.toOracleNDTM_wellFormed M.wf⟩

end Turing
