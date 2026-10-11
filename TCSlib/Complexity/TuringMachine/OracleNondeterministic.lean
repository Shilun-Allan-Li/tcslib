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
  machine ignores its choices (proved; the lockstep obligation of phase P3.1).

* `Turing.OracleNDTM.fixChoice` — the deterministic machine at a fixed choice bit.
* `Turing.OracleNDTM.stepWith_eq_fixChoice_step` — the fixed-choice step bridge.
* `Turing.OracleNDTM.stepWith_eq_of_ne_qQuery` — oracle independence off the query state.
* `Turing.OracleNDTM.runWith_workTapes_invariant` — initialized head and blank-cell bounds.
* `Turing.OracleNDTM.queryString_runWith_length_le` — the branchwise query-length bound.

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

/-- An embedded deterministic oracle step agrees with the original step under
either choice bit.

**Proof sketch.** Unfold the two step definitions once and split on the state;
the halted, query and ordinary branches have identical fields. -/
private theorem toOracleNDTM_stepWith (M : OracleTM k Symbol State)
    (O : Language Symbol) (b : Bool) (cfg : Cfg (k + 1) Symbol State input) :
    M.toOracleNDTM.stepWith O b cfg = M.step O cfg := by
  unfold OracleNDTM.stepWith OracleTM.step
  cases hs : cfg.state <;> rfl

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
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih =>
    show M.toOracleNDTM.runWith O w (M.toOracleNDTM.stepWith O b cfg) =
      M.runFrom O (M.step O cfg) w.length
    rw [toOracleNDTM_stepWith]
    exact ih (M.step O cfg)

/-- Fixing the choice bit of a nondeterministic oracle machine gives a
deterministic oracle machine with the same initial and special states.
[AB09, Definition 3.4]

**Proof sketch.** Keep the four states and select the transition table at `b`. -/
def OracleNDTM.fixChoice (N : OracleNDTM k Symbol State) (b : Bool) :
    OracleTM k Symbol State := ⟨N.q₀, N.qQuery, N.qYes, N.qNo, N.tr b⟩

/-- A nondeterministic oracle step under bit `b` is the deterministic step of
the machine with its choice fixed to `b`.

**Proof sketch.** Apply the deterministic embedding's step identity to the
fixed-choice machine; the nondeterministic steps are definitionally equal. -/
theorem OracleNDTM.stepWith_eq_fixChoice_step (N : OracleNDTM k Symbol State)
    (O : Language Symbol) (b : Bool) (cfg : Cfg (k + 1) Symbol State input) :
    N.stepWith O b cfg = (N.fixChoice b).step O cfg :=
  toOracleNDTM_stepWith (N.fixChoice b) O b cfg

/-- Away from the query state, a nondeterministic step under a fixed bit is
independent of the oracle.

**Proof sketch.** Pass through the fixed-choice machine and cite deterministic
oracle independence away from the query state. -/
theorem OracleNDTM.stepWith_eq_of_ne_qQuery {N : OracleNDTM k Symbol State}
    (O₁ O₂ : Language Symbol) {b : Bool} {cfg : Cfg (k + 1) Symbol State input}
    (h : cfg.state ≠ some N.qQuery) : N.stepWith O₁ b cfg = N.stepWith O₂ b cfg := by
  rw [OracleNDTM.stepWith_eq_fixChoice_step, OracleNDTM.stepWith_eq_fixChoice_step]
  exact OracleTM.step_eq_of_ne_qQuery (M := N.fixChoice b) O₁ O₂ h

/-- Heads bounded by `n` and cells blank at distance at least `n` remain bounded
and blank beyond the enlarged radius `n + w.length` after a branch run.

**Proof sketch.** Induct on the choice word, generalizing the starting
configuration and radius. Through the fixed-choice bridge, the deterministic
one-step bounds increase the head radius by one and preserve cells outside
that new radius, since they differ from the old head. Apply the induction
hypothesis to the suffix. -/
private theorem runWith_headBlank (N : OracleNDTM k Symbol State)
    (O : Language Symbol) (w : List Bool) (n : ℕ)
    (cfg : Cfg (k + 1) Symbol State input)
    (hpos : ∀ i, |cfg.workTapePos i| ≤ (n : ℤ))
    (hblank : ∀ i (z : ℤ), (n : ℤ) ≤ |z| → cfg.workTapes i z = none) :
    (∀ i, |(N.runWith O w cfg).workTapePos i| ≤ ((n + w.length : ℕ) : ℤ)) ∧
      ∀ i (z : ℤ), ((n + w.length : ℕ) : ℤ) ≤ |z| →
        (N.runWith O w cfg).workTapes i z = none := by
  induction w generalizing n cfg with
  | nil => simpa only [OracleNDTM.runWith_nil, List.length_nil, Nat.add_zero] using
      And.intro hpos hblank
  | cons b w ih =>
    have nextPos : ∀ i, |(N.stepWith O b cfg).workTapePos i| ≤ ((n + 1 : ℕ) : ℤ) := by
      intro i
      rw [OracleNDTM.stepWith_eq_fixChoice_step]
      have move := (N.fixChoice b).workTapePos_step_le O cfg i
      have old := hpos i
      rw [abs_le] at move old ⊢
      omega
    have nextBlank : ∀ i (z : ℤ), ((n + 1 : ℕ) : ℤ) ≤ |z| →
        (N.stepWith O b cfg).workTapes i z = none := by
      intro i z hz
      have different : z ≠ cfg.workTapePos i := by
        intro heq
        have old := hpos i
        rw [← heq] at old
        omega
      rw [OracleNDTM.stepWith_eq_fixChoice_step,
        (N.fixChoice b).workTapes_step_eq_of_ne O i different]
      exact hblank i z (by omega)
    have suffix := ih (n + 1) (N.stepWith O b cfg) nextPos nextBlank
    simpa only [OracleNDTM.runWith_cons, List.length_cons,
      Nat.add_assoc, Nat.add_comm 1 w.length] using suffix

/-- After an initialized branch run, every work head is within the number of
steps of the origin, and every cell at least that far from the origin is blank.
[AB09, proof of Theorem 3.7, applied branchwise]

**Proof sketch.** Specialize the generalized head/blank invariant to radius
zero: initially every work head is at zero and every work tape is blank. -/
theorem OracleNDTM.runWith_workTapes_invariant (N : OracleNDTM k Symbol State)
    (O : Language Symbol) (x : List Symbol) (w : List Bool) :
    (∀ i, |(N.runWith O w (N.initCfg x)).workTapePos i| ≤ (w.length : ℤ)) ∧
      ∀ i (z : ℤ), (w.length : ℤ) ≤ |z| → (N.runWith O w (N.initCfg x)).workTapes i z = none := by
  simpa only [Nat.zero_add] using
    runWith_headBlank N O w 0 (N.initCfg x) (by intro i; simp)
      (by intro i z _; rfl)

/-- The query string after an initialized nondeterministic branch run has length
at most the length of the choice word. [AB09, proof of Theorem 3.7, branchwise]

**Proof sketch.** The initialized invariant keeps the query cell at the branch
length blank. The blank-cell bound then bounds the extracted query.

**C1-P1 appendix.** The blank-cell bound is the public
`Turing.OracleTM.queryString_length_le_of_blank`, promoted from this file. -/
theorem OracleNDTM.queryString_runWith_length_le (N : OracleNDTM k Symbol State)
    (O : Language Symbol) (x : List Symbol) (w : List Bool) :
    (OracleTM.queryString (N.runWith O w (N.initCfg x))).length ≤ w.length := by
  exact OracleTM.queryString_length_le_of_blank _ w.length
    ((N.runWith_workTapes_invariant O x w).2 _ _ (le_abs_self _))

/-- A bundled deterministic oracle machine as a bundled nondeterministic one, with
the same tapes, state type, and special states. -/
def FinOracleTM.toFinOracleNDTM {Symbol : Type} (M : FinOracleTM Symbol) :
    FinOracleNDTM Symbol :=
  ⟨M.k, M.State, M.tm.toOracleNDTM, OracleTM.toOracleNDTM_wellFormed M.wf⟩

end Turing
