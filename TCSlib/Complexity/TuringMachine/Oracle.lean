/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Deterministic
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle Turing machines

An oracle Turing machine [AB09, §3.4, Definition 3.4; pulled forward to Chapter 1 to
validate the model architecture] is a multi-tape machine with one additional designated
*query tape* and three designated states `qQuery`, `qYes`, `qNo`. Whenever the machine
enters `qQuery`, the string currently written on the query tape is submitted to the oracle
`O`: in a single step the machine moves to `qYes` if the query is in `O` and to `qNo`
otherwise, with all tapes and heads unchanged.

## Design

This file is the architectural test of the `Action`/`Action.apply` split: an oracle machine
reuses the configurations `Turing.Cfg (k + 1)` (the query tape is the extra work tape, at
index `Fin.last k`) and the action application of the plain model, and differs *only* in how
the next action is chosen — the step function is parametrized by the oracle
`O : Language Symbol`. Time and space measures therefore transfer unchanged.

Definitional choices worth auditing:

* **The query string** (`OracleTM.queryString`) is read from cell `0` of the query tape
  rightward up to (excluding) the first blank cell; if the whole nonnegative half-tape is
  blank-free (possible for an arbitrary configuration, though not for one reachable from an
  initial configuration), the query is defined to be `[]`. [AB09] leaves the extraction
  convention implicit; this is one concrete faithful reading.
* **The answer step** changes only the state; heads and tapes stay put. Some texts
  instead erase the query tape on each answer. The two conventions are equivalent up to
  *polynomial* overhead, but **not** constant overhead: computing the parity of `n`
  distinct length-`n` queries takes `O(n)` steps with a persistent tape and `Ω(n²)`
  steps with auto-erasure (`audits/phase1-findings.md`, finding 3, case 12).
  Consequently, exact `DTIME`-level bounds must never be transferred across this
  convention; class-level results (`Pᴼ` etc.) are unaffected.
* `qYes`/`qNo` are ordinary states from the machine's point of view (its transition
  function handles them); only `qQuery` triggers special behavior. The machine may query
  repeatedly. This reading presumes the three special states are pairwise distinct,
  which the raw structure does not enforce (e.g. with `qYes = qQuery` the machine
  re-queries forever after a positive answer): results at the faithful interface assume
  `OracleTM.WellFormed`. Note that
  `q₀ = qQuery` is legitimate and deliberately allowed (the machine then submits the
  empty query on its first step).

## Main definitions

* `Turing.OracleTM` — the oracle machine. [AB09, Definition 3.4]
* `Turing.OracleTM.WellFormed` — the three special states are pairwise distinct; the
  standing hypothesis of the faithful interface (oracle complexity classes will require
  it).
* `Turing.OracleTM.step`, `Turing.OracleTM.runFrom` — semantics relative to an oracle.
* `Turing.OracleTM.ComputesInTime` — output and time bound relative to an oracle.
* `Turing.Action.extend`, `Turing.Cfg.embedOracle`, `Turing.OracleTM.ofMultiTapeTM` —
  the embedding of plain machines as oracle machines that never query (state renaming
  via `Turing.Action.mapState`, now in `TCSlib.Complexity.TuringMachine.StateRenaming`).
* `Turing.OracleTM.plainEmptyOracle` — the converse direction: an oracle machine run
  with the empty oracle, as a plain `k + 1`-tape machine in exact lockstep.

## Main results (sanity checks for the architecture)

* `Turing.OracleTM.step_eq_of_ne_qQuery` — away from `qQuery`, the step does not depend
  on the oracle.
* `Turing.OracleTM.ofMultiTapeTM_wellFormed` — the embedding produces well-formed
  machines.
* `Turing.OracleTM.runFrom_ofMultiTapeTM` — an embedded plain machine runs in lockstep
  with the original, under every oracle.
* `Turing.OracleTM.computesInTime_ofMultiTapeTM` — hence its input/output behavior and
  time bounds are oracle-independent and agree with the plain machine's.
* `Turing.OracleTM.runFrom_plainEmptyOracle` — the empty-oracle elimination runs in
  exact lockstep.
* `Turing.OracleTM.queryString_length_le` — in an initialized run, the query after `t`
  steps has length at most `t`.
* `Turing.OracleTM.runFrom_workTapes_blank` — in an initialized run, cells at distance
  `≥ t` are still blank after `t` steps; the certificate that the no-blank fallback in
  `queryString` is unreachable from initialization.
* `Turing.OracleTM.queryString_length_le_of_blank`, `Turing.OracleTM.queryString_eq_of_cells`
  — the extraction contract: a blank query cell bounds the query, and a query tape holding
  `w` from cell `0` with a blank at `|w|` reads back exactly `w` (the first promoted from
  C1c's private bound, backlog C1-P1; added 2026-10-11, B1).
* `Turing.OracleTM.step_of_halt`, `Turing.OracleTM.runFrom_succ_eq_step'`,
  `Turing.OracleTM.runFrom_add`, `Turing.OracleTM.runFrom_of_halt`,
  `Turing.OracleTM.runFrom_comm_of_step`, `Turing.OracleTM.ComputesInTime.mono`,
  `Turing.OracleTM.ComputesInTime.output_unique` — the oracle run algebra, mirroring the
  plain machine's (added 2026-10-11, B1).
* `Turing.OracleTM.runFrom_eq_of_forall_ne_qQuery`, `Turing.OracleTM.runFrom_eq_plainEmptyOracle`
  — a run that never sits in `qQuery` is oracle-independent from any configuration, and is
  then the run of the plain table `plainEmptyOracle`: the bridge through which the
  plain-machine library contracts apply to an oracle machine on its query-free segments
  (added 2026-10-11, B1).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4: oracle machines; Definition 3.4.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- An oracle Turing machine with `k` ordinary work tapes, one query tape (the work tape
of index `Fin.last k` in its configurations `Cfg (k + 1)`), and designated query and
answer states. Finiteness of `State` is deferred exactly as for `MultiTapeTM`, and so is
distinctness of the three special states: the raw structure allows them to coincide
(with degenerate behavior, e.g. `qYes = qQuery` re-queries forever after a positive
answer), and the faithful interface imposes `OracleTM.WellFormed`.
[AB09, Definition 3.4] -/
structure OracleTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- entering this state submits the query tape's contents to the oracle -/
  qQuery : State
  /-- the state the oracle answer step moves to on a positive answer -/
  qYes : State
  /-- the state the oracle answer step moves to on a negative answer -/
  qNo : State
  /-- transition function on the `k + 1` work tapes (the last being the query tape);
  consulted in every state except `qQuery` -/
  tr (q : State) (input : Option Symbol) (work : Fin (k + 1) → Option Symbol) :
    Action (k + 1) Symbol State

namespace OracleTM

variable {M : OracleTM k Symbol State}

/-- Well-formedness of an oracle machine: the query state and the two answer states are
pairwise distinct. Without this, the advertised semantics degenerates: with
`qYes = qQuery` a positive answer re-queries the unchanged tape forever (a negative
answer may still reach a distinct `qNo` and halt normally), and with all three states
collapsed the machine loops once the common query state is reached (an initial state
elsewhere can still halt via the table without ever querying). Moreover `qYes = qNo`
alone makes the step function — hence every run — oblivious to the oracle. This is the
standing hypothesis of the faithful oracle interface —
oracle complexity classes will require it. `q₀ = qQuery` is deliberately allowed: such a
machine simply submits the empty query on its first step.
(`audits/phase1-findings.md`, finding 2.) -/
structure WellFormed (M : OracleTM k Symbol State) : Prop where
  /-- the query state is not the positive-answer state -/
  qQuery_ne_qYes : M.qQuery ≠ M.qYes
  /-- the query state is not the negative-answer state -/
  qQuery_ne_qNo : M.qQuery ≠ M.qNo
  /-- the two answer states are distinct -/
  qYes_ne_qNo : M.qYes ≠ M.qNo

/-- The index of the query tape among the `k + 1` work tapes. -/
def queryTapeIdx (k : ℕ) : Fin (k + 1) := Fin.last k

open Classical in
/-- The query string of a configuration: the contents of the query tape from cell `0`
rightward, up to (excluding) the first blank cell. If no blank cell exists on the
nonnegative half-tape — impossible in configurations reachable from an initial
configuration, but possible for an arbitrary one — the query is `[]`. -/
noncomputable def queryString (cfg : Cfg (k + 1) Symbol State input) : List Symbol :=
  if h : ∃ n : ℕ, cfg.workTapes (queryTapeIdx k) (n : ℤ) = none then
    (List.range (Nat.find h)).filterMap fun n => cfg.workTapes (queryTapeIdx k) (n : ℤ)
  else []

open Classical in
/-- One step of the oracle machine `M` relative to the oracle `O`. In state `qQuery` the
machine moves to `qYes` or `qNo` according to whether the current query string is in `O`,
leaving tapes, head positions and output unchanged; in every other state it steps by its
transition function exactly like a plain machine. [AB09, §3.4] -/
noncomputable def step (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) : Cfg (k + 1) Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q =>
    if q = M.qQuery then
      { cfg with state := some (if queryString cfg ∈ O then M.qYes else M.qNo) }
    else
      (M.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The initial configuration of an oracle machine: all `k + 1` work tapes (including the
query tape) blank. -/
@[simp]
def initCfg (M : OracleTM k Symbol State) (input : List Symbol) :
    Cfg (k + 1) Symbol State input :=
  Cfg.init M.q₀ input

/-- The configuration reached by running `M` with oracle `O` for `t` steps from `cfg`. -/
noncomputable def runFrom (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (t : ℕ) : Cfg (k + 1) Symbol State input :=
  (M.step O)^[t] cfg

/-- `M` with oracle `O` halts on `input` within `t` steps with `output` on its output
tape. Time-only, mirroring `Turing.FinTM.ComputesInTime`. -/
def ComputesInTime (M : OracleTM k Symbol State) (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) : Prop :=
  (M.runFrom O (M.initCfg input) t).state = none ∧
  (M.runFrom O (M.initCfg input) t).output = output

/-- Away from the query state, a step of an oracle machine does not depend on the oracle. -/
theorem step_eq_of_ne_qQuery (O₁ O₂ : Language Symbol)
    {cfg : Cfg (k + 1) Symbol State input} (h : cfg.state ≠ some M.qQuery) :
    M.step O₁ cfg = M.step O₂ cfg := by
  unfold step
  cases hs : cfg.state with
  | none => rfl
  | some q =>
    have hne : q ≠ M.qQuery := fun hq => h (by rw [hs, hq])
    dsimp only
    rw [if_neg hne, if_neg hne]

/-- A halted configuration is fixed by the oracle step, under every oracle: halting is
absorbing, as for plain machines (`Turing.MultiTapeTM.step_of_halt`). [AB09, §3.4] -/
@[simp]
theorem step_of_halt (M : OracleTM k Symbol State) (O : Language Symbol)
    {cfg : Cfg (k + 1) Symbol State input} (h : cfg.state = none) : M.step O cfg = cfg := by
  unfold step; rw [h]

/-- One more step of an oracle run is one oracle step from the configuration reached:
`runFrom O cfg (t + 1) = step O (runFrom O cfg t)`, the oracle counterpart of
`Turing.MultiTapeTM.runFrom_succ_eq_step'`. -/
theorem runFrom_succ_eq_step' (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (t : ℕ) :
    M.runFrom O cfg (t + 1) = M.step O (M.runFrom O cfg t) :=
  Function.iterate_succ_apply' _ _ _

/-- Oracle runs compose: running `a + b` steps is running `b` steps from the configuration
reached after `a`, under the same oracle (the counterpart of
`Turing.MultiTapeTM.runFrom_add`). -/
theorem runFrom_add (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (a b : ℕ) :
    M.runFrom O cfg (a + b) = M.runFrom O (M.runFrom O cfg a) b := by
  unfold runFrom
  rw [show a + b = b + a from Nat.add_comm a b, Function.iterate_add_apply]

/-- A halted configuration is fixed by every oracle run, under every oracle. -/
theorem runFrom_of_halt (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (h : cfg.state = none) {n : ℕ} :
    M.runFrom O cfg n = cfg :=
  Function.iterate_fixed (step_of_halt M O h) n

/-- **Time monotonicity**: if `M` with oracle `O` produces `out` from `x` within `t`
steps, it does so within any `t' ≥ t` steps, halting being absorbing (the oracle
counterpart of `Turing.FinTM.ComputesInTime.mono`). [AB09, §3.4]

**Proof sketch.** Factor the run to `t'` through `t` (`runFrom_add`); the configuration
at `t` is halted, so `runFrom_of_halt` fixes it. -/
theorem ComputesInTime.mono {M : OracleTM k Symbol State} {O : Language Symbol}
    {x out : List Symbol} {t t' : ℕ} (h : M.ComputesInTime O x out t) (hle : t ≤ t') :
    M.ComputesInTime O x out t' := by
  obtain ⟨hh, ho⟩ := h
  have hrun : M.runFrom O (M.initCfg x) t' = M.runFrom O (M.initCfg x) t := by
    rw [← Nat.add_sub_of_le hle, runFrom_add, runFrom_of_halt M O _ hh]
  exact ⟨hrun ▸ hh, hrun ▸ ho⟩

/-- **Determinism of completed outputs**: relative to a fixed oracle, a machine has at
most one completed output on a given input; computations of `w` and of `w'` from `x`
force `w = w'`. [AB09, §3.4]

**Proof sketch.** Absorb both computations to the later time (`ComputesInTime.mono`);
both outputs are then the output of one and the same configuration. -/
theorem ComputesInTime.output_unique {M : OracleTM k Symbol State} {O : Language Symbol}
    {x w w' : List Symbol} {t t' : ℕ} (h : M.ComputesInTime O x w t)
    (h' : M.ComputesInTime O x w' t') : w = w' := by
  have h₁ := h.mono (Nat.le_max_left t t')
  have h₂ := h'.mono (Nat.le_max_right t t')
  rw [← h₁.2, ← h₂.2]

/-- **Run commutation from step commutation**: a map of configurations that commutes with
one oracle step of two machines (each under its own oracle) commutes with their runs,
the oracle counterpart of `Turing.MultiTapeTM.runFrom_comm_of_step`. -/
theorem runFrom_comm_of_step {k' : ℕ} {State' : Type*} {input' : List Symbol}
    {M : OracleTM k Symbol State} {M' : OracleTM k' Symbol State'} {O O' : Language Symbol}
    (f : Cfg (k + 1) Symbol State input → Cfg (k' + 1) Symbol State' input')
    (hstep : ∀ cfg, M'.step O' (f cfg) = f (M.step O cfg))
    (cfg : Cfg (k + 1) Symbol State input) (n : ℕ) :
    M'.runFrom O' (f cfg) n = f (M.runFrom O cfg n) :=
  (Function.Semiconj.iterate_right (fun c => (hstep c).symm) n cfg).symm

/-- **Oracle independence of query-free runs**, from any configuration: if the run with
oracle `O` never sits in `qQuery` before time `t`, its first `t` steps are the same under
every other oracle `O'`. [AB09, §3.4: the oracle is consulted only in the query state]

**Proof sketch.** Induction on `t`: equal configurations at time `s`, not in the query
state, take equal steps by `step_eq_of_ne_qQuery`. -/
theorem runFrom_eq_of_forall_ne_qQuery (M : OracleTM k Symbol State) (O O' : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (t : ℕ)
    (h : ∀ s < t, (M.runFrom O cfg s).state ≠ some M.qQuery) :
    M.runFrom O cfg t = M.runFrom O' cfg t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runFrom_succ_eq_step', runFrom_succ_eq_step', ← ih (fun s hs => h s (by omega))]
    exact step_eq_of_ne_qQuery O O' (h t (by omega))

/-- Applying any action changes a work-tape cell only at the old head position. -/
private lemma apply_workTapes_eq_of_ne {k' : ℕ} (a : Action k' Symbol State)
    (cfg : Cfg k' Symbol State input) (i : Fin k') {z : ℤ}
    (hz : z ≠ cfg.workTapePos i) :
    (a.apply cfg).workTapes i z = cfg.workTapes i z := by
  dsimp only [Action.apply]
  rcases h : (a.workTapes i).1 with _ | s
  · rfl
  · exact Function.update_of_ne hz _ _

/-- A work-tape head moves by at most one cell in a single oracle step. -/
lemma workTapePos_step_le (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (i : Fin (k + 1)) :
    |(M.step O cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  unfold step
  split
  · simp
  · split
    · simp
    · exact workTapePos_apply_le _ cfg i

/-- An oracle step writes only at the old head position. -/
lemma workTapes_step_eq_of_ne (M : OracleTM k Symbol State) (O : Language Symbol)
    {cfg : Cfg (k + 1) Symbol State input} (i : Fin (k + 1)) {z : ℤ}
    (hz : z ≠ cfg.workTapePos i) :
    (M.step O cfg).workTapes i z = cfg.workTapes i z := by
  unfold step
  split
  · rfl
  · split
    · rfl
    · exact apply_workTapes_eq_of_ne _ cfg i hz

/-- The two run invariants of an initialized oracle run: after `t` steps every work
head is within distance `t` of the origin, and every cell at distance at least `t` is
still blank. -/
private lemma runFrom_workTapes_invariant (M : OracleTM k Symbol State)
    (O : Language Symbol) (x : List Symbol) : ∀ t : ℕ,
    (∀ i, |(M.runFrom O (M.initCfg x) t).workTapePos i| ≤ (t : ℤ)) ∧
    (∀ i (z : ℤ), (t : ℤ) ≤ |z| → (M.runFrom O (M.initCfg x) t).workTapes i z = none) := by
  intro t
  induction t with
  | zero =>
    constructor
    · intro i
      simp [runFrom]
    · intro i z _
      simp [runFrom]
  | succ t ih =>
    obtain ⟨hpos, hblank⟩ := ih
    have hstep : M.runFrom O (M.initCfg x) (t + 1) =
        M.step O (M.runFrom O (M.initCfg x) t) :=
      Function.iterate_succ_apply' _ _ _
    constructor
    · intro i
      rw [hstep]
      have h1 := M.workTapePos_step_le O (M.runFrom O (M.initCfg x) t) i
      have h2 := hpos i
      rw [abs_le] at h1 h2 ⊢
      omega
    · intro i z hz
      rw [hstep]
      have hz' : (t : ℤ) ≤ |z| := le_trans (by omega) hz
      have hne : z ≠ (M.runFrom O (M.initCfg x) t).workTapePos i := by
        intro hzeq
        have h2 := hpos i
        rw [← hzeq] at h2
        have h3 : ((t : ℤ) + 1) ≤ |z| := by exact_mod_cast hz
        have h4 := le_trans h3 h2
        omega
      rw [M.workTapes_step_eq_of_ne O i hne]
      exact hblank i z hz'

/-- **A blank query cell bounds the query**: if the query tape of any configuration is
blank at the nonnegative cell `n`, the extracted query has length at most `n`, extraction
stopping at the first blank. Promoted from a private lemma of
`TCSlib.Complexity.TuringMachine.OracleNondeterministic` (backlog C1-P1).

**Proof sketch.** The least blank exists, with witness `n`, and is at most `n`
(`Nat.find_le`); filtering the preceding range cannot increase its length. -/
theorem queryString_length_le_of_blank (cfg : Cfg (k + 1) Symbol State input)
    (n : ℕ) (h : cfg.workTapes (OracleTM.queryTapeIdx k) (n : ℤ) = none) :
    (OracleTM.queryString cfg).length ≤ n := by
  classical
  rw [OracleTM.queryString, dif_pos ⟨n, h⟩]
  refine (List.length_filterMap_le _ _).trans ?_
  simpa using (Nat.find_le (h := ⟨n, h⟩) h)

/-- **The extraction contract**: if the query tape holds the word `w` in cells
`0, …, |w| - 1` and is blank at cell `|w|`, the extracted query is exactly `w`, whatever
lies beyond cell `|w|` or at negative cells. [AB09, Definition 3.4, with this file's
extraction convention `queryString`]

**Proof sketch.** Cell `|w|` is the first blank, the earlier cells holding symbols; by
induction on `m ≤ |w|`, filtering the first `m` cells yields the length-`m` prefix of `w`.
(The definition lifts `List.range` into `ℤ` through the list monad, which is first
rewritten to a `List.map`.) -/
theorem queryString_eq_of_cells (cfg : Cfg (k + 1) Symbol State input) (w : List Symbol)
    (hw : ∀ i (hi : i < w.length), cfg.workTapes (queryTapeIdx k) (i : ℤ) = some w[i])
    (hb : cfg.workTapes (queryTapeIdx k) (w.length : ℤ) = none) :
    queryString cfg = w := by
  classical
  have hex : ∃ n : ℕ, cfg.workTapes (queryTapeIdx k) (n : ℤ) = none := ⟨w.length, hb⟩
  have hfind : Nat.find hex = w.length := by
    apply le_antisymm (Nat.find_min' hex hb)
    by_contra hlt
    push_neg at hlt
    have := Nat.find_spec hex
    rw [hw _ hlt] at this
    exact Option.some_ne_none _ this
  rw [queryString, dif_pos hex, hfind]
  have key : ∀ m ≤ w.length, (List.range m).filterMap
      (fun n : ℕ => cfg.workTapes (queryTapeIdx k) (n : ℤ)) = w.take m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.filterMap_append, ih (by omega), List.take_succ,
        List.getElem?_eq_getElem (by omega)]
      simp [hw m (by omega)]
  have hmap : ∀ l : List ℕ,
      (do let a ← l; pure (a : ℤ) : List ℤ) = l.map (fun a : ℕ => (a : ℤ)) := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons] at ih ⊢; rw [← ih]; rfl
  rw [hmap, List.filterMap_map]
  exact (key w.length le_rfl).trans List.take_length

/-- In an initialized run, the query after `t` steps has length at most `t`. In
particular the no-blank fallback branch of `queryString` is unreachable from an initial
configuration.

**Proof sketch.** By induction on `t`, every write performed in the first `t` steps
happened at a head position of absolute value at most `t - 1` (heads start at `0` and
move at most one cell per step, `Turing.workTapePos_apply_le`). Hence cell `t` of the
query tape is still blank at time `t`, so the least-blank search in `queryString`
terminates at an index `≤ t`.

**C1-P1 appendix.** That last step is the shared blank-cell bound
`Turing.OracleTM.queryString_length_le_of_blank`. -/
theorem queryString_length_le (M : OracleTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (t : ℕ) :
    (queryString (M.runFrom O (M.initCfg x) t)).length ≤ t :=
  queryString_length_le_of_blank _ t
    ((runFrom_workTapes_invariant M O x t).2 _ _ (le_abs_self _))

/-- In an initialized run, every work-tape cell at distance at least `t` from the
origin is still blank after `t` steps. This is the certificate that the no-blank
fallback branch of `queryString` is unreachable from initialization (the length bound
`queryString_length_le` alone does not certify this, since the fallback also returns a
short list).

**Proof sketch.** Simultaneous induction on `t` with the head-position bound
`|workTapePos i| ≤ t`: at `t = 0` all tapes are blank and heads are at `0`; an ordinary
step writes only at the *old* head position (of absolute value `≤ t`, hence `< t + 1`;
`Action.apply` writes before moving) and moves each head by at most one cell
(`Turing.workTapePos_apply_le`); oracle-answer and halted steps change no tape. -/
theorem runFrom_workTapes_blank (M : OracleTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (t : ℕ) (i : Fin (k + 1)) (z : ℤ) (hz : (t : ℤ) ≤ |z|) :
    (M.runFrom O (M.initCfg x) t).workTapes i z = none :=
  (runFrom_workTapes_invariant M O x t).2 i z hz

end OracleTM

/-- Extend an action on `k` work tapes to `k + 1` work tapes: the extra (last) tape is
neither written nor moved. -/
def Action.extend (a : Action k Symbol State) : Action (k + 1) Symbol State where
  inputTape := a.inputTape
  workTapes := fun i =>
    if h : (i : ℕ) < k then a.workTapes ⟨i, h⟩ else (none, 0)
  output := a.output
  state := a.state

/-- Embed a `k`-tape configuration into a `k + 1`-tape configuration over the extended
state type `State ⊕ Fin 3`: the extra work tape is blank with its head at `0`, and the
state is renamed along `Sum.inl`. -/
def Cfg.embedOracle (cfg : Cfg k Symbol State input) :
    Cfg (k + 1) Symbol (State ⊕ Fin 3) input where
  state := cfg.state.map Sum.inl
  inputPos := cfg.inputPos
  workTapes := fun i =>
    if h : (i : ℕ) < k then cfg.workTapes ⟨i, h⟩ else fun _ => none
  workTapePos := fun i => if h : (i : ℕ) < k then cfg.workTapePos ⟨i, h⟩ else 0
  output := cfg.output

/-- The embedding preserves the scanned input symbol. -/
lemma Cfg.embedOracle_inputSymbol (cfg : Cfg k Symbol State input) :
    cfg.embedOracle.inputSymbol = cfg.inputSymbol := rfl

/-- The embedding preserves the scanned work symbols on the original tapes. -/
lemma Cfg.embedOracle_workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) :
    cfg.embedOracle.workTapeSymbols i.castSucc = cfg.workTapeSymbols i := by
  simp [Cfg.workTapeSymbols, Cfg.embedOracle]

/-- The embedding preserves haltedness. -/
lemma Cfg.embedOracle_state_eq_none {cfg : Cfg k Symbol State input} :
    cfg.embedOracle.state = none ↔ cfg.state = none := by
  simp [Cfg.embedOracle, Option.map_eq_none_iff]

/-- The embedding preserves the output tape. -/
lemma Cfg.embedOracle_output (cfg : Cfg k Symbol State input) :
    cfg.embedOracle.output = cfg.output := rfl

/-- Applying an extended, state-renamed action to an embedded configuration is the
embedding of applying the original action. -/
lemma Cfg.embedOracle_apply (a : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    ((a.mapState (Sum.inl : State → State ⊕ Fin 3)).extend).apply cfg.embedOracle =
      (a.apply cfg).embedOracle := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simp [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle]
  · simp [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle]
  · funext i
    by_cases hi : (i : ℕ) < k
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_pos hi]
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_neg hi]
  · funext i
    by_cases hi : (i : ℕ) < k
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_pos hi]
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_neg hi]
      simp
  · simp [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle]

/-- The embedding sends initial configurations to initial configurations. -/
lemma Cfg.embedOracle_init (q₀ : State) (input : List Symbol) :
    (Cfg.init q₀ input : Cfg k Symbol State input).embedOracle =
      Cfg.init (Sum.inl q₀ : State ⊕ Fin 3) input := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [Cfg.embedOracle]

namespace OracleTM

/-- Embed a plain machine as an oracle machine that never queries: the state type is
extended by three fresh states serving as `qQuery`, `qYes`, `qNo`, and the transition
function acts as before on original states (never moving into the fresh states, and
ignoring the query tape). The fresh states are unreachable from the initial
configuration. The *transition table* halts immediately from all three fresh states;
note that from `qQuery` itself the query override fires first (one answer step into
`qYes`/`qNo`, whose table entries then halt) — the table's `qQuery` row is dead code. -/
def ofMultiTapeTM (tm : MultiTapeTM k Symbol State) : OracleTM k Symbol (State ⊕ Fin 3) where
  q₀ := .inl tm.q₀
  qQuery := .inr 0
  qYes := .inr 1
  qNo := .inr 2
  tr q inp work :=
    match q with
    | .inl q => ((tm.tr q inp fun i => work i.castSucc).mapState Sum.inl).extend
    | .inr _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- The embedding of a plain machine is well-formed: its three fresh special states are
pairwise distinct by construction. -/
theorem ofMultiTapeTM_wellFormed (tm : MultiTapeTM k Symbol State) :
    (ofMultiTapeTM tm).WellFormed := by
  constructor <;> simp [ofMultiTapeTM]

/-- One step of an embedded plain machine, under any oracle, is the embedding of one
step of the original machine: the embedded state is never `qQuery = Sum.inr 0`, so the
oracle step reduces to applying the extended action, and `Cfg.embedOracle_apply` turns
that into the embedding of the original step. -/
lemma step_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg k Symbol State input) :
    (ofMultiTapeTM tm).step O cfg.embedOracle = (tm.step cfg).embedOracle := by
  unfold OracleTM.step MultiTapeTM.step
  cases hs : cfg.state with
  | none =>
    have h : cfg.embedOracle.state = none := by simp [Cfg.embedOracle, hs]
    rw [h]
  | some q =>
    have h : cfg.embedOracle.state = some (Sum.inl q) := by simp [Cfg.embedOracle, hs]
    rw [h]
    dsimp only
    have hne : (Sum.inl q : State ⊕ Fin 3) ≠ (ofMultiTapeTM tm).qQuery := by
      simp [ofMultiTapeTM]
    rw [if_neg hne]
    have hw : (fun i => cfg.embedOracle.workTapeSymbols i.castSucc) =
        cfg.workTapeSymbols :=
      funext fun i => Cfg.embedOracle_workTapeSymbols cfg i
    have htr : (ofMultiTapeTM tm).tr (Sum.inl q) cfg.embedOracle.inputSymbol
        cfg.embedOracle.workTapeSymbols =
        ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).mapState Sum.inl).extend := by
      show ((tm.tr q cfg.embedOracle.inputSymbol
        fun i => cfg.embedOracle.workTapeSymbols i.castSucc).mapState Sum.inl).extend = _
      rw [Cfg.embedOracle_inputSymbol, hw]
    rw [htr, Cfg.embedOracle_apply]

/-- **Sanity check for the oracle architecture** (plan §3.1): an embedded plain machine
runs in lockstep with the original under every oracle — `step_ofMultiTapeTM` pointwise,
then induction on `t`. -/
theorem runFrom_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (ofMultiTapeTM tm).runFrom O cfg.embedOracle t = (tm.runFrom cfg t).embedOracle := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : (ofMultiTapeTM tm).runFrom O cfg.embedOracle (t + 1) =
        (ofMultiTapeTM tm).step O ((ofMultiTapeTM tm).runFrom O cfg.embedOracle t) :=
      Function.iterate_succ_apply' _ _ _
    rw [h1, ih, MultiTapeTM.runFrom_succ_eq_step', step_ofMultiTapeTM]

/-- An embedded plain machine has the same input/output behavior and time bounds as the
original, relative to every oracle. In particular its behavior is oracle-independent.

**Proof sketch.** `Cfg.embedOracle` sends the initial configuration of `tm` to the initial
configuration of the embedded machine (both have blank work tapes and heads at `0`); by
`runFrom_ofMultiTapeTM` the runs correspond, and `Cfg.embedOracle` preserves haltedness
and the output tape. -/
theorem computesInTime_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) :
    (ofMultiTapeTM tm).ComputesInTime O input output t ↔
      ((tm.runFrom (tm.initCfg input) t).state = none ∧
        (tm.runFrom (tm.initCfg input) t).output = output) := by
  have hinit : (ofMultiTapeTM tm).initCfg input = (tm.initCfg input).embedOracle := by
    simp only [OracleTM.initCfg, MultiTapeTM.initCfg, ofMultiTapeTM]
    exact (Cfg.embedOracle_init tm.q₀ input).symm
  simp only [OracleTM.ComputesInTime, hinit, runFrom_ofMultiTapeTM,
    Cfg.embedOracle_state_eq_none, Cfg.embedOracle_output]

open Classical in
/-- The converse of `ofMultiTapeTM` for the empty oracle: an oracle machine run with the
empty oracle is eliminated into a plain `k + 1`-tape machine over the *same* state type,
by replacing the query behavior with a stationary transition into `qNo` (the empty
oracle always answers no). (`audits/phase1-findings.md`, finding 8.) -/
noncomputable def plainEmptyOracle (M : OracleTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol State where
  q₀ := M.q₀
  tr q inp work :=
    if q = M.qQuery then ⟨0, fun _ => (none, 0), none, some M.qNo⟩
    else M.tr q inp work

/-- One step of the empty-oracle elimination coincides with one step of the oracle
machine on the empty oracle: on a halted configuration both sides are fixed; in state
`qQuery` the empty oracle answers `qNo` and the stationary action's `Action.apply`
changes only the state; elsewhere both sides apply the same transition-table action. -/
lemma step_plainEmptyOracle (M : OracleTM k Symbol State)
    (cfg : Cfg (k + 1) Symbol State input) :
    M.plainEmptyOracle.step cfg = M.step (0 : Language Symbol) cfg := by
  unfold MultiTapeTM.step OracleTM.step plainEmptyOracle
  cases hs : cfg.state with
  | none => rfl
  | some q =>
    dsimp only
    by_cases hq : q = M.qQuery
    · rw [if_pos hq, if_pos hq, if_neg (Language.notMem_zero _)]
      refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [Action.apply]
    · rw [if_neg hq, if_neg hq]

/-- **Sanity check, converse direction**: the empty-oracle elimination runs in exact
lockstep with the oracle machine on the empty oracle — same configurations at every
step, from every starting configuration (`step_plainEmptyOracle` pointwise, then
induction on `t`). -/
theorem runFrom_plainEmptyOracle (M : OracleTM k Symbol State)
    (cfg : Cfg (k + 1) Symbol State input) (t : ℕ) :
    -- `0` is the empty language (`Language`'s `Zero` instance)
    M.plainEmptyOracle.runFrom cfg t = M.runFrom (0 : Language Symbol) cfg t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : M.runFrom (0 : Language Symbol) cfg (t + 1) =
        M.step 0 (M.runFrom (0 : Language Symbol) cfg t) :=
      Function.iterate_succ_apply' _ _ _
    rw [MultiTapeTM.runFrom_succ_eq_step', h1, ih, step_plainEmptyOracle]

/-- **The transfer bridge**: while the run of the plain table `plainEmptyOracle` from `cfg`
avoids `qQuery`, the oracle run under *any* oracle `O` is that plain run. Hence the
plain-machine library contracts (W1 capture, the R1/R2 rows, the catalog) apply to an
oracle machine on the run segments where it does not query.

**Proof sketch.** The plain run is the run under the empty oracle
(`runFrom_plainEmptyOracle`); a run under the empty oracle that avoids `qQuery` is the
run under `O` (`runFrom_eq_of_forall_ne_qQuery`). -/
theorem runFrom_eq_plainEmptyOracle (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (t : ℕ)
    (h : ∀ s < t, (M.plainEmptyOracle.runFrom cfg s).state ≠ some M.qQuery) :
    M.runFrom O cfg t = M.plainEmptyOracle.runFrom cfg t := by
  rw [runFrom_plainEmptyOracle]
  refine (runFrom_eq_of_forall_ne_qQuery M 0 O cfg t fun s hs => ?_).symm
  rw [← runFrom_plainEmptyOracle]
  exact h s hs

end OracleTM

end Turing
