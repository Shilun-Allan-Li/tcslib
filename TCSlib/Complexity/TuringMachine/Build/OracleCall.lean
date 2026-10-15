/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.OracleNondeterministic
import TCSlib.Complexity.TuringMachine.Build.Wrappers

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: oracle-machine rows

The oracle-machine rows of the machine-construction library
(`machine-library-design.md` §12.9). The §12 library is stated for plain machines;
these rows let its contracts drive oracle machines `Turing.OracleTM` [AB09,
Definition 3.4]: capturing a computation onto the **query tape** and submitting it, and
the **answer tail** that turns the oracle's verdict into an output bit. They are the
query-capture and query-tail halves of the one-query constructions of [AB09, §3.4]
(`Complexity.mem_POracle_of_polyTimeReducible`, `Complexity.unaryWitnessLang_mem_NPOracle`).

## Design

* **Capture onto the query tape is W1 verbatim.** `Turing.captureAction` writes the
  source's emissions on the host's *last* work tape, which in an oracle machine is the
  query tape `Turing.OracleTM.queryTapeIdx`. It silences the physical output and sends the
  halting transition to a designated state; taking that state to be `qQuery` submits the
  completed output as the query on the very transition after the source's final step. No
  seam glue is needed.
* **Plain contracts reach the oracle host through the transfer bridge**
  `Turing.OracleTM.runFrom_eq_plainEmptyOracle` (`TCSlib.Complexity.TuringMachine.Oracle`):
  on run segments that avoid `qQuery` the oracle run is the run of a plain table, so
  `Turing.capture_run` applies unchanged.
* **The answer tail is two steps.** The query step moves to `qYes`/`qNo` with tapes
  unchanged; a row `answerAction b` there emits `b` and halts. Nondeterministic machines
  use the same rows through `Turing.OracleNDTM.fixChoice`.

## Main definitions

* `Turing.OracleTM.answerAction` — the emit-and-halt action of the answer tail.

## Main results

* `Turing.OracleTM.queryString_bufferTape` — a buffered query tape reads back verbatim.
* `Turing.OracleTM.step_of_qQuery`, `Turing.OracleTM.step_of_answerAction`,
  `Turing.OracleTM.runFrom_two_of_qQuery` — the query step, the answer step, and the
  two-step tail.
* `Turing.OracleTM.capture_reaches_qQuery` — W1 under an oracle host: a halting source,
  captured onto the query tape, reaches the query state with its whole output as the
  query by its halting time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Definition 3.4, Example 3.6, Theorem 3.7.)
-/

namespace Turing

namespace OracleTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- A query tape holding the buffered word `w` (cells `0, …, |w| - 1`, blank elsewhere)
submits exactly `w`. [AB09, Definition 3.4]

**Proof sketch.** The extraction contract `Turing.OracleTM.queryString_eq_of_cells`, read
off `Turing.FinTM.bufferTape_nat`. -/
theorem queryString_bufferTape (cfg : Cfg (k + 1) Symbol State input) (w : List Symbol)
    (h : cfg.workTapes (queryTapeIdx k) = FinTM.bufferTape w) : queryString cfg = w :=
  queryString_eq_of_cells cfg w
    (fun i hi => by rw [h, FinTM.bufferTape_nat, List.getElem?_eq_getElem hi])
    (by rw [h, FinTM.bufferTape_nat, List.getElem?_eq_none le_rfl])

open Classical in
/-- **The query step**: in state `qQuery` an oracle machine moves to `qYes` or `qNo`
according to whether the current query belongs to the oracle, with tapes, heads, and
output unchanged. [AB09, Definition 3.4] -/
theorem step_of_qQuery (M : OracleTM k Symbol State) (O : Language Symbol)
    {cfg : Cfg (k + 1) Symbol State input} (h : cfg.state = some M.qQuery) :
    M.step O cfg = { cfg with
      state := some (if queryString cfg ∈ O then M.qYes else M.qNo) } := by
  unfold step; rw [h]; simp

/-- The answer action of the four-state query tail: emit `b` and halt, touching no tape
and not moving the input head. -/
def answerAction (b : Symbol) : Action (k + 1) Symbol State :=
  ⟨0, fun _ => (none, 0), some b, none⟩

/-- **The answer step**: in a live state `q ≠ qQuery` whose transition row is
`answerAction b`, one step halts with `b` appended to the output and every other field
unchanged. -/
theorem step_of_answerAction (M : OracleTM k Symbol State) (O : Language Symbol)
    {cfg : Cfg (k + 1) Symbol State input} {q : State} {b : Symbol}
    (hs : cfg.state = some q) (hq : q ≠ M.qQuery)
    (htr : ∀ inp w, M.tr q inp w = answerAction b) :
    M.step O cfg = { cfg with state := none, output := cfg.output ++ [b] } := by
  unfold step
  rw [hs]
  simp only [if_neg hq, htr]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · simp [answerAction, Action.apply]
  · funext i; simp [answerAction, Action.apply]
  · funext i; simp [answerAction, Action.apply]

open Classical in
/-- **The two-step answer tail** [AB09, Example 3.6, the one-query machines]: a
well-formed oracle machine whose `qYes` and `qNo` rows emit `yes` and `no` and halt, from
a configuration in `qQuery`, halts two steps later having appended the oracle's verdict
on the current query (`yes` if the query is in `O`, else `no`), all tapes unchanged.

**Proof sketch.** `step_of_qQuery`, then `step_of_answerAction` at `qYes` or `qNo`, both
distinct from `qQuery` by well-formedness. -/
theorem runFrom_two_of_qQuery (M : OracleTM k Symbol State) (hwf : M.WellFormed)
    {yes no : Symbol}
    (hyes : ∀ inp w, M.tr M.qYes inp w = answerAction yes)
    (hno : ∀ inp w, M.tr M.qNo inp w = answerAction no)
    (O : Language Symbol) {cfg : Cfg (k + 1) Symbol State input}
    (hq : cfg.state = some M.qQuery) :
    M.runFrom O cfg 2 =
      { cfg with
        state := none
        output := cfg.output ++ [if queryString cfg ∈ O then yes else no] } := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, runFrom_succ_eq_step', runFrom_succ_eq_step']
  change M.step O (M.step O cfg) = _
  rw [M.step_of_qQuery O hq]
  by_cases hm : queryString cfg ∈ O
  · simp only [if_pos hm]
    rw [M.step_of_answerAction O rfl (Ne.symm hwf.qQuery_ne_qYes) hyes]
  · simp only [if_neg hm]
    rw [M.step_of_answerAction O rfl (Ne.symm hwf.qQuery_ne_qNo) hno]

/-- **Query-tape capture** (W1 under an oracle host) [AB09, §3.4, the one-query
machines]: let an oracle machine `M` agree, on an embedded copy of a plain source's
states that avoids `qQuery`, with the W1-transformed source table whose return state is
`qQuery`. If the source halts from `c₀` by time `T`, then at some time `u ≤ T` the host,
started from the capture image of `c₀`, sits at the capture image of the source's
halted configuration: in `qQuery`, with the source's whole output (after the prefix
`pre`) buffered on the query tape and the host's physical output still `out₀`.

**Proof sketch.** Take the source's first halting time `u ≤ T`
(`Turing.MultiTapeTM.exists_first_halt`). On the plain table `M.plainEmptyOracle`, which
agrees with `M` off `qQuery`, `Turing.capture_run` gives the capture image at every time
up to `u`. Before `u` those images sit in embedded source states, never `qQuery`, so the
transfer bridge `Turing.OracleTM.runFrom_eq_plainEmptyOracle` makes the oracle run under
`O` equal to the plain run. -/
theorem capture_reaches_qQuery {S H : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (M : OracleTM k Bool H) (O : Language Bool)
    (emb : S → H) (hemb : ∀ s, emb s ≠ M.qQuery)
    (hagree : ∀ (s : S) (inp : Option Bool) (w : Fin (k + 1) → Option Bool),
      M.tr (emb s) inp w = captureAction emb M.qQuery (tm.tr s inp fun i => w i.castSucc))
    (pre out₀ : List Bool) (c₀ : Cfg k Bool S x) (T : ℕ)
    (hhalt : (tm.runFrom c₀ T).state = none) :
    ∃ u ≤ T, M.runFrom O (captureCfg emb M.qQuery pre out₀ c₀) u =
      captureCfg emb M.qQuery pre out₀ (tm.runFrom c₀ T) := by
  obtain ⟨u, hle, hlive, hend⟩ := tm.exists_first_halt c₀ hhalt
  have hP : ∀ (s : S) (inp : Option Bool) (w : Fin (k + 1) → Option Bool),
      M.plainEmptyOracle.tr (emb s) inp w =
        captureAction emb M.qQuery (tm.tr s inp fun i => w i.castSucc) := by
    intro s inp w
    simp only [plainEmptyOracle, if_neg (hemb s)]
    exact hagree s inp w
  have hcap : ∀ v ≤ u,
      M.plainEmptyOracle.runFrom (captureCfg emb M.qQuery pre out₀ c₀) v =
        captureCfg emb M.qQuery pre out₀ (tm.runFrom c₀ v) := fun v hv =>
    capture_run tm M.plainEmptyOracle emb M.qQuery hP pre out₀ c₀ v
      (fun t' ht' => hlive t' (by omega))
  refine ⟨u, hle, ?_⟩
  rw [M.runFrom_eq_plainEmptyOracle O _ _ ?_, hcap _ le_rfl, hend]
  intro s hs
  rw [hcap s hs.le]
  cases hst : (tm.runFrom c₀ s).state with
  | none => exact absurd hst (hlive s hs)
  | some q =>
    simp only [captureCfg, hst, Option.map_some, Option.getD_some]
    exact fun h => hemb q (Option.some.inj h)

end OracleTM

end Turing
