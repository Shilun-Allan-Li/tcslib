/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Diagonalization.EXPCOM
import TCSlib.Complexity.TuringMachine.OracleAgreement

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Baker-Gill-Solovay relativization theorem

[AB09, Theorem 3.7] ([BGS75]): there are oracles `A` and `B` with
`P^A = NP^A` and `P^B ≠ NP^B` — so no proof technique that relativizes can
resolve `P` vs `NP`. The `A` half is the `EXPCOM` cluster
(`Diagonalization/EXPCOM`, [AB09, Example 3.6(3)]). The `B` half is this file:
the unary witness language `U_B` is in `NP^B` for every `B` (guess the
witness, ask the oracle), and a stage construction diagonalizes `B` against an
enumeration of deterministic polynomial-time oracle machines so that
`U_B ∉ P^B`.

## Design

* **Extrinsic clocks** ([BGS75, p. 432]; `AroraBarakChapters3-4Plan.md` §7,
  question 4): [BGS75] requires its enumerated machines' polynomial clocks to
  be meaningful under *every* oracle, whereas
  `Turing.FinOracleTM.DecidesInTime` is a promise about one oracle only. The
  enumeration statement below therefore never mentions `DecidesInTime`: it
  speaks of raw `Turing.FinOracleTM.ComputesInTime` horizons (explicit step
  budgets in the style of `Turing.FinOracleNDTM.AcceptsWithin`, oracle-uniform
  by construction), and the stage construction attaches the budget
  `fun n => n ^ i + i` to the index `i` extrinsically.
* **The enumeration is of deterministic machines**: the diagonalization runs
  against the would-be `P^B` deciders, so `Turing.FinOracleTM Bool` is
  enumerated; no universal oracle machine is needed
  (`AroraBarakChapters3-4Plan.md` §2.3).
* **Behavioral equality** ("runs coincide under every oracle") is rendered as
  equality of `ComputesInTime` verdicts at every oracle, input, output, and
  horizon — the state types of two bundled machines differ, so literal
  configuration equality is not expressible, and this observable form is
  exactly what the stage construction consumes.
* **The stage construction is mathematics, not machine-building**: its engine
  is the locality layer of `TCSlib.Complexity.TuringMachine.OracleAgreement`
  (query-set locality, the query-length bound, and the at-most-`t`-queries
  counting bound).

## Main definitions

* `Complexity.unaryWitnessLang` — the book's `U_B`. [AB09, Theorem 3.7]

## Main results (one statement remains sorried: `baker_gill_solovay`, cluster B5)

* `Complexity.unaryWitnessLang_mem_NPOracle` — `U_B ∈ NP^B`, for every `B`.
* `Complexity.exists_finOracleTM_enumeration` — an enumeration of the
  deterministic finite oracle machines in which every machine recurs at
  arbitrarily late indices, up to behavioral equality under every oracle.
  [BGS75, p. 432]
* `Complexity.exists_oracle_ne` — the stage construction: some `B` has
  `U_B ∈ NP^B \ P^B`. [AB09, Theorem 3.7; BGS75, §3]
* `Complexity.baker_gill_solovay` — both halves assembled.
  [AB09, Theorem 3.7]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Theorem 3.7, pp. 74-75.)
* [BGS75] T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP
  question*, SIAM Journal on Computing 4(4), 1975. (pp. 431-433: the
  all-oracle clock convention; §3: the stage construction.)
-/

namespace Complexity

open Turing

/-- **The unary witness language** `U_B` of [AB09, Theorem 3.7]: the unary
strings `1ⁿ` such that `B` contains some string of length exactly `n`. Finding
the witness is one nondeterministic guess with oracle access to `B`, but a
deterministic polynomial-time machine can examine only polynomially many of
the `2ⁿ` candidates. -/
def unaryWitnessLang (B : Language Bool) : Language Bool :=
  {w | ∃ n : ℕ, w = List.replicate n true ∧ ∃ x : List Bool, x.length = n ∧ x ∈ B}

/-- The table of the `Complexity.unaryWitnessLang_mem_NPOracle` machine (the P3.2 audit's
four-state construction, answer 7), with no ordinary work tapes, so the query tape is the
only one. State `0` scans: on input `true` it writes the current choice bit on the query
tape and advances both heads; on `false` it emits `false` and halts; on the input's end it
enters the query state `1` without writing. States `2`/`3` (yes/no) emit their verdict
and halt. Hand-built: the machine library has no oracle nondeterministic guess-writer
row; the answer rows are the library's `Turing.OracleTM.answerAction`. -/
private def uwTable : OracleNDTM 0 Bool (Fin 4) where
  q₀ := 0
  qQuery := 1
  qYes := 2
  qNo := 3
  tr b q inp _ :=
    if q = 0 then
      match inp with
      | some true => ⟨SignType.pos, fun _ => (some (some b), SignType.pos), none, some 0⟩
      | some false => OracleTM.answerAction false
      | none => ⟨0, fun _ => (none, 0), none, some 1⟩
    else if q = 2 then OracleTM.answerAction true
    else OracleTM.answerAction false

/-- The bundled, well-formed unary-witness machine. -/
private def uwTM : FinOracleNDTM Bool :=
  ⟨0, Fin 4, uwTable, ⟨by decide, by decide, by decide⟩⟩

/-- The scan invariant after `j` steps: in state `0`, input head on the `j`-th symbol, the
guessed bits `u` buffered on the query tape with its head at `j`, nothing emitted. -/
private def uwScanCfg {x : List Bool} (j : ℕ) (hj : j ≤ x.length) (u : List Bool) :
    Cfg (0 + 1) Bool (Fin 4) x :=
  ⟨some 0, ⟨j + 1, by omega⟩, fun _ => FinTM.bufferTape u, fun _ => (j : ℤ), []⟩

/-- The configuration at the input's end, in the query state. -/
private def uwQueryCfg {x : List Bool} (u : List Bool) : Cfg (0 + 1) Bool (Fin 4) x :=
  ⟨some 1, ⟨x.length + 1, by omega⟩, fun _ => FinTM.bufferTape u, fun _ => (x.length : ℤ),
    []⟩

/-- The initial configuration is the scan invariant at `j = 0`. -/
private theorem uw_init (x : List Bool) :
    uwTable.initCfg x = uwScanCfg 0 (Nat.zero_le _) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z; simp [uwScanCfg]
  · funext i; simp [uwScanCfg]

/-- The one unfolding of `stepWith` at the scan state: it applies the scan row. -/
private theorem uw_step_scan (B : Language Bool) {x : List Bool}
    (c : Cfg (0 + 1) Bool (Fin 4) x) (hs : c.state = some 0) (b : Bool) :
    uwTable.stepWith B b c = (uwTable.tr b 0 c.inputSymbol c.workTapeSymbols).apply c := by
  unfold OracleNDTM.stepWith
  rw [hs]
  exact if_neg (by decide : (0 : Fin 4) ≠ uwTable.qQuery)

/-- One write-and-advance step on a `true` input symbol. -/
private theorem uw_scan_step (B : Language Bool) {x : List Bool} (j : ℕ) (hj : j < x.length)
    (hx : x[j] = true) (u : List Bool) (hu : u.length = j) (b : Bool) :
    uwTable.stepWith B b (uwScanCfg j hj.le u) = uwScanCfg (j + 1) hj (u ++ [b]) := by
  rw [uw_step_scan B _ rfl, inputSymbolInner j (by simp [uwScanCfg]; omega) hj, hx]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    simp only [uwTable, if_pos, Action.apply, uwScanCfg]
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext i
    simp only [uwTable, if_pos, Action.apply, uwScanCfg]
    rw [FinTM.bufferTape_append, hu]
  · funext i
    simp [uwTable, Action.apply, uwScanCfg]

/-- A one-bit choice word is one step. -/
private theorem uw_runWith_single (B : Language Bool) (b : Bool) {x : List Bool}
    (c : Cfg (0 + 1) Bool (Fin 4) x) : uwTable.runWith B [b] c = uwTable.stepWith B b c := rfl

/-- **The guess-writer contract**: on an input whose first `j` symbols are `true`, the
first `j` choice bits are written on the query tape, one per step.

**Proof sketch.** Induction on `j`, splitting `w.take (j + 1)` into `w.take j` and the
next bit (`Turing.OracleNDTM.runWith_append`), then one write-and-advance step. -/
private theorem uw_scan_run (B : Language Bool) {x : List Bool} (w : List Bool) :
    ∀ j (hj : j ≤ x.length), (∀ i (hi : i < j), x[i]'(by omega) = true) → j ≤ w.length →
      uwTable.runWith B (w.take j) (uwTable.initCfg x) = uwScanCfg j hj (w.take j) := by
  intro j
  induction j with
  | zero => intro _ _ _; simp only [List.take_zero, OracleNDTM.runWith_nil]; exact uw_init x
  | succ j ih =>
    intro hj hpre hw
    rw [List.take_succ, List.getElem?_eq_getElem (by omega), Option.toList_some,
      OracleNDTM.runWith_append, ih (by omega) (fun i hi => hpre i (by omega)) (by omega),
      uw_runWith_single]
    exact uw_scan_step B j (by omega) (hpre j (by omega)) _ (by simp; omega) _

/-- At the input's end the scan enters the query state, nothing written. -/
private theorem uw_end_step (B : Language Bool) {x : List Bool} (u : List Bool) (b : Bool) :
    uwTable.stepWith B b (uwScanCfg x.length le_rfl u) = uwQueryCfg (x := x) u := by
  have hin : (uwScanCfg (x := x) x.length le_rfl u).inputSymbol = none := by
    simp [Cfg.inputSymbol, uwScanCfg]
  rw [uw_step_scan B _ rfl, hin]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl <;> simp [uwTable, Action.apply, uwScanCfg, uwQueryCfg]

/-- A `false` input symbol rejects at once, on every branch. -/
private theorem uw_false_step (B : Language Bool) {x : List Bool} (j : ℕ) (hj : j < x.length)
    (hx : x[j] = false) (u : List Bool) (b : Bool) :
    (uwTable.stepWith B b (uwScanCfg j hj.le u)).state = none ∧
      (uwTable.stepWith B b (uwScanCfg j hj.le u)).output = [false] := by
  rw [uw_step_scan B _ rfl, inputSymbolInner j (by simp [uwScanCfg]; omega) hj, hx]
  exact ⟨rfl, rfl⟩

open Classical in
/-- **Query and answer**: from the query configuration with guess `u` buffered, two more
bits halt the branch with output `[u ∈ B]`.

**Proof sketch.** Through the fixed-choice step (`stepWith_eq_fixChoice_step`): the query
step reads exactly `u` (`queryString_bufferTape`), then the answer row emits and halts
(`step_of_answerAction`). -/
private theorem uw_tail (B : Language Bool) {x : List Bool} (u : List Bool) (b₁ b₂ : Bool) :
    (uwTable.runWith B [b₁, b₂] (uwQueryCfg (x := x) u)).state = none ∧
    (uwTable.runWith B [b₁, b₂] (uwQueryCfg (x := x) u)).output =
      [if u ∈ B then true else false] := by
  have hq : OracleTM.queryString (uwQueryCfg (x := x) u) = u :=
    OracleTM.queryString_bufferTape _ u rfl
  simp only [OracleNDTM.runWith_cons, OracleNDTM.runWith_nil]
  rw [OracleNDTM.stepWith_eq_fixChoice_step uwTable B b₁,
    OracleTM.step_of_qQuery (uwTable.fixChoice b₁) B rfl, hq,
    OracleNDTM.stepWith_eq_fixChoice_step uwTable B b₂]
  by_cases hu : u ∈ B
  · simp only [if_pos hu]
    rw [OracleTM.step_of_answerAction (uwTable.fixChoice b₂) B rfl
      (show (2 : Fin 4) ≠ 1 by decide) (fun _ _ => rfl)]
    exact ⟨rfl, rfl⟩
  · simp only [if_neg hu]
    rw [OracleTM.step_of_answerAction (uwTable.fixChoice b₂) B rfl
      (show (3 : Fin 4) ≠ 1 by decide) (fun _ _ => rfl)]
    exact ⟨rfl, rfl⟩

open Classical in
/-- **The per-branch verdict**: every branch of length at least `|x| + 3` has halted, and
it outputs `[true]` exactly when `x` is all `true` and its first `|x|` bits form a word of
`B`.

**Proof sketch.** If `x` is all `true`, split the word as the guess, the end-of-input bit,
two tail bits and the rest: the guess-writer contract, the end step and the tail give a
halted configuration, which absorbs the rest. Otherwise take the first `false` position
`j`: the scan reaches it after `j` bits and the next bit rejects; the branch outputs
`[false]`. -/
private theorem uw_branch (B : Language Bool) (x w : List Bool) (hw : x.length + 3 ≤ w.length) :
    (uwTable.runWith B w (uwTable.initCfg x)).state = none ∧
    ((uwTable.runWith B w (uwTable.initCfg x)).output = [true] ↔
      (∀ i (hi : i < x.length), x[i] = true) ∧ w.take x.length ∈ B) := by
  by_cases hall : ∀ i (hi : i < x.length), x[i] = true
  · have hsplit : w = w.take x.length ++ ([w[x.length]] ++
        ([w[x.length + 1], w[x.length + 2]] ++ w.drop (x.length + 3))) := by
      conv_lhs => rw [← List.take_append_drop x.length w]
      congr 1
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
        List.drop_eq_getElem_cons (by omega)]
      rfl
    have hscan := uw_scan_run B w x.length le_rfl (fun i hi => hall i hi) (by omega)
    obtain ⟨hh, ho⟩ := uw_tail B (x := x) (w.take x.length) w[x.length + 1] w[x.length + 2]
    have hrun : uwTable.runWith B w (uwTable.initCfg x) =
        uwTable.runWith B [w[x.length + 1], w[x.length + 2]]
          (uwQueryCfg (x := x) (w.take x.length)) := by
      conv_lhs => rw [hsplit]
      rw [OracleNDTM.runWith_append, OracleNDTM.runWith_append, OracleNDTM.runWith_append,
        hscan, uw_runWith_single, uw_end_step, OracleNDTM.runWith_of_halt B _ hh]
    rw [hrun]
    refine ⟨hh, ?_⟩
    rw [ho]
    by_cases hb : w.take x.length ∈ B
    · simp [hb, hall]
    · simp [hb]
  · push_neg at hall
    let hex : ∃ j, ∃ hj : j < x.length, x[j] = false := by
      obtain ⟨i, hi, hx⟩ := hall
      exact ⟨i, hi, by simpa using hx⟩
    obtain ⟨hjlt, hjx⟩ := Nat.find_spec hex
    set j := Nat.find hex
    have hpre : ∀ i (hi : i < j), x[i]'(by omega) = true := by
      intro i hi
      have := Nat.find_min hex hi
      push_neg at this
      have h2 := this (by omega)
      simpa using h2
    have hsplit : w = w.take j ++ ([w[j]'(by omega)] ++ w.drop (j + 1)) := by
      conv_lhs => rw [← List.take_append_drop j w]
      rw [List.drop_eq_getElem_cons (by omega)]
      rfl
    have hscan := uw_scan_run B w j hjlt.le hpre (by omega)
    obtain ⟨hh, ho⟩ := uw_false_step B j hjlt hjx (w.take j) (w[j]'(by omega))
    have hrun : uwTable.runWith B w (uwTable.initCfg x) =
        uwTable.stepWith B (w[j]'(by omega)) (uwScanCfg j hjlt.le (w.take j)) := by
      conv_lhs => rw [hsplit]
      rw [OracleNDTM.runWith_append, OracleNDTM.runWith_append, hscan, uw_runWith_single,
        OracleNDTM.runWith_of_halt B _ hh]
    rw [hrun]
    refine ⟨hh, ?_⟩
    rw [ho]
    simp only [List.cons.injEq, Bool.false_eq_true, and_true, false_iff, not_and]
    intro hall'
    exact absurd (hjx.symm.trans (hall' _ _)) Bool.false_ne_true

/-- **`U_B ∈ NP^B`, for every oracle `B`**: guess a string of the input's
length onto the query tape, query, and accept on a positive answer.
[AB09, Theorem 3.7, the easy half: "`U_B` is clearly in `NP^B`"]

**Proof sketch.** A small well-formed `Turing.FinOracleNDTM Bool`: scan the
input left to right, rejecting on every branch if any input symbol is `false`
(so non-unary inputs are out), and at each input position write the current
choice bit onto the query tape and advance both heads — the choice word *is*
the guessed witness ([AB09, §2.1.2], the certificate reading of choice words);
at the input boundary enter `qQuery`; from `qYes` emit `[true]` and halt, from
`qNo` emit `[false]` and halt. Budget: a constant times `n + 1`, inside
`NPOracle`'s `c · (n^1 + 1)` normal form; every branch runs the same number of
steps, so all-branch halting (`Turing.OracleNDTM.HaltsWithin`) holds at the
budget. Correctness, per branch along `Turing.OracleNDTM.runWith`: the string
read back by `Turing.OracleTM.queryString` at the query step is exactly the
first `n` choice bits (a write-and-advance invariant on the query tape — the
guess-writer contract), so on input `1ⁿ` some branch accepts iff some length-`n`
string lies in `B`, i.e. iff `1ⁿ ∈ U_B` (`Complexity.unaryWitnessLang`), and
on non-unary inputs no branch accepts. Fill obligations, named for the brief:
the guess-writer machine and its query-tape read-back contract; the four-state
answer tail shared with `Complexity.mem_POracle_of_polyTimeReducible`'s
obligation (ii) (flagged as a shared routine for the §12 catalog); the budget
arithmetic and `Turing.FinOracleNDTM.DecidesInTime` assembly.

**B1 appendix.** The answer tail is the library's `Turing.OracleTM.answerAction` with
`Turing.OracleTM.step_of_qQuery`/`step_of_answerAction`, through the fixed-choice step;
the guess is read back by `Turing.OracleTM.queryString_bufferTape`. The witness is
exponent `1` and constant `3`. -/
theorem unaryWitnessLang_mem_NPOracle (B : Language Bool) :
    unaryWitnessLang B ∈ NPOracle B := by
  classical
  refine Set.mem_iUnion.mpr ⟨1, 3, uwTM, fun x => ⟨?_, ?_⟩⟩
  · intro w hw
    exact (uw_branch B x w (by simp only [pow_one] at hw; omega)).1
  · constructor
    · rintro ⟨n, rfl, y, hy, hyB⟩
      refine ⟨y ++ List.replicate (2 * n + 3) false, ?_, ?_⟩
      · simp only [List.length_append, List.length_replicate, hy, pow_one]; omega
      · have hb := uw_branch B (List.replicate n true) (y ++ List.replicate (2 * n + 3) false)
          (by simp only [List.length_append, List.length_replicate, hy]; omega)
        refine ⟨hb.1, hb.2.mpr ⟨fun i hi => by simp, ?_⟩⟩
        simpa [hy] using hyB
    · rintro ⟨w, hw, -, ho⟩
      have hb := uw_branch B x w (by simp only [pow_one] at hw; omega)
      obtain ⟨hall, hB⟩ := hb.2.mp ho
      refine ⟨x.length, ?_, w.take x.length, ?_, hB⟩
      · apply List.eq_replicate_iff.mpr
        refine ⟨rfl, fun b hb' => ?_⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb'
        exact hall i hi
      · simp only [List.length_take]; simp only [pow_one] at hw; omega

/-- R1: transport an oracle table along a state equivalence. The ordinary
transition uses `Action.mapState`; all distinguished states are transported.
The received relabelling API covers only plain machines, so this oracle
version is requested for `TuringMachine/Oracle.lean` when a second consumer
appears. -/
private def oracleRelabel {k : ℕ} {Symbol S S' : Type*}
    (tm : OracleTM k Symbol S) (e : S ≃ S') : OracleTM k Symbol S' where
  q₀ := e tm.q₀
  qQuery := e tm.qQuery
  qYes := e tm.qYes
  qNo := e tm.qNo
  tr q inp work := (tm.tr (e.symm q) inp work).mapState e

/-- R1: injectivity preserves the three required state inequalities. -/
private theorem oracleRelabel_wellFormed {k : ℕ} {Symbol S S' : Type*}
    (tm : OracleTM k Symbol S) (e : S ≃ S') (wf : tm.WellFormed) :
    (oracleRelabel tm e).WellFormed := by
  exact ⟨e.injective.ne wf.qQuery_ne_qYes,
    e.injective.ne wf.qQuery_ne_qNo, e.injective.ne wf.qYes_ne_qNo⟩

/-- R1: one oracle step commutes with state relabelling, including the
query-answer branch and absorbing halted configurations.

**Proof sketch.** Split the optional state. A halted configuration is fixed.
At the query state, injectivity identifies the same query branch; the query
string ignores the state, and mapping the answer commutes with its conditional.
Elsewhere the inverse equivalence recovers the original table row, and
`Cfg.mapState_apply` transports its action. This is the single step argument
used by all later run and behavior transfers. -/
private theorem oracleRelabel_step {k : ℕ} {Symbol S S' : Type*}
    {x : List Symbol} (tm : OracleTM k Symbol S) (e : S ≃ S')
    (O : Language Symbol) (cfg : Cfg (k + 1) Symbol S x) :
    (oracleRelabel tm e).step O (cfg.mapState e) = (tm.step O cfg).mapState e := by
  classical
  unfold OracleTM.step
  cases hs : cfg.state with
  | none => simp only [Cfg.mapState, hs, Option.map_none]
  | some q =>
      simp only [Cfg.mapState, hs, Option.map_some, oracleRelabel, e.injective.eq_iff]
      by_cases hq : q = tm.qQuery
      · rw [if_pos hq, if_pos hq]
        refine Cfg.ext ?_ rfl rfl rfl rfl
        change some (if OracleTM.queryString cfg ∈ O then e tm.qYes else e tm.qNo) =
          some (e (if OracleTM.queryString cfg ∈ O then tm.qYes else tm.qNo))
        rw [apply_ite e]
      · rw [if_neg hq, if_neg hq]
        simpa only [Equiv.symm_apply_apply] using
          Cfg.mapState_apply e (tm.tr q cfg.inputSymbol cfg.workTapeSymbols) cfg

/-- R1: arbitrary-start oracle runs commute with state relabelling, by the
standard iteration theorem applied to the single step commutation. -/
private theorem oracleRelabel_runFrom {k : ℕ} {Symbol S S' : Type*}
    {x : List Symbol} (tm : OracleTM k Symbol S) (e : S ≃ S')
    (O : Language Symbol) (cfg : Cfg (k + 1) Symbol S x) (t : ℕ) :
    (oracleRelabel tm e).runFrom O (cfg.mapState e) t =
      (tm.runFrom O cfg t).mapState e := by
  have h : Function.Semiconj (Cfg.mapState (input := x) e)
      (tm.step O) ((oracleRelabel tm e).step O) :=
    fun c => (oracleRelabel_step tm e O c).symm
  exact (h.iterate_right t cfg).symm

/-- R1: relabelling preserves every oracle-relative time-bounded output
verdict. Initialization transports definitionally; run transport preserves
output, and `Option.map_eq_none_iff` preserves haltedness. -/
private theorem oracleRelabel_computesInTime {k : ℕ} {Symbol S S' : Type*}
    (tm : OracleTM k Symbol S) (e : S ≃ S') (O : Language Symbol)
    (x out : List Symbol) (t : ℕ) :
    (oracleRelabel tm e).ComputesInTime O x out t ↔ tm.ComputesInTime O x out t := by
  have hinit : (oracleRelabel tm e).initCfg x = (tm.initCfg x).mapState e := rfl
  simp only [OracleTM.ComputesInTime, hinit, oracleRelabel_runFrom]
  simp only [Cfg.mapState, Option.map_eq_none_iff]

/-- R2: well-formed binary oracle tables over the canonical state type. -/
private abbrev CanonTab (k n : ℕ) :=
  {tm : OracleTM k Bool (Fin n) // tm.WellFormed}

set_option synthInstance.maxSize 1024 in
/-- R2: one named finiteness structure for canonical tables. All later ranks
and cardinalities use this structure explicitly to avoid instance diamonds.

**Proof sketch.** Inject the well-formed subtype into the tuple of its four
state fields and the transition table's four action fields. Each coordinate
is finite. Tuple injectivity, function extensionality and the two structure
constructor injectivity lemmas recover the original table. The oracle and
action layers do not yet supply this finiteness API; its requested shared
home is `TuringMachine/Oracle.lean` at a second consumer. -/
private noncomputable def canonTabFintype (k n : ℕ) : Fintype (CanonTab k n) := by
  let fields : OracleTM k Bool (Fin n) →
      Fin n × Fin n × Fin n × Fin n ×
        (Fin n → Option Bool → (Fin (k + 1) → Option Bool) →
          SignType × (Fin (k + 1) → Option (Option Bool) × SignType) ×
            Option Bool × Option (Fin n)) :=
    fun tm => ⟨tm.q₀, tm.qQuery, tm.qYes, tm.qNo, fun q inp work =>
      ⟨(tm.tr q inp work).inputTape, (tm.tr q inp work).workTapes,
        (tm.tr q inp work).output, (tm.tr q inp work).state⟩⟩
  refine Fintype.ofInjective (fun x : CanonTab k n => fields x.val) ?_
  intro a b hab
  apply Subtype.ext
  rcases a with ⟨⟨a₀, aQ, aY, aN, ta⟩, wa⟩
  rcases b with ⟨⟨b₀, bQ, bY, bN, tb⟩, wb⟩
  simp only [fields, Prod.mk.injEq] at hab
  rcases hab with ⟨h₀, hQ, hY, hN, ht⟩
  simp only [OracleTM.mk.injEq]
  refine ⟨h₀, hQ, hY, hN, ?_⟩
  funext q inp work
  have hrow := congrFun (congrFun (congrFun ht q) inp) work
  cases ha : ta q inp work
  cases hb : tb q inp work
  simpa only [ha, hb, Prod.mk.injEq, Action.mk.injEq] using hrow

/-- R3: the well-formed three-state fallback starts in the yes state and
halts on its first ordinary transition. No oracle-table default is supplied
by the construction layer; this explicit table totalizes invalid ranks. -/
private def oracleDefault : FinOracleTM Bool :=
  ⟨0, Fin 3, ⟨1, 0, 1, 2, fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩,
    ⟨by decide, by decide, by decide⟩⟩

/-- R4: select a canonical table at an explicit rank, with the fixed
fallback for rank overflow. Keeping the three coordinates as arguments lets
the decoder simplify its pairing before opening the dependent rank branch. -/
private noncomputable def oracleTableAt (k n r : ℕ) : FinOracleTM Bool :=
  if h : r < @Fintype.card (CanonTab k n) (canonTabFintype k n) then
    let table := (@Fintype.equivFin (CanonTab k n) (canonTabFintype k n)).symm ⟨r, h⟩
    ⟨k, Fin n, table.val, table.property⟩
  else oracleDefault

/-- R4: decode the tape count, state count and rank using two pairings. -/
private noncomputable def decodeOracleTable (j : ℕ) : FinOracleTM Bool :=
  oracleTableAt (Nat.unpair j).1 (Nat.unpair (Nat.unpair j).2).1
    (Nat.unpair (Nat.unpair j).2).2

/-- R4: the code made from a canonical table's rank decodes to that table.

**Proof sketch.** Unpair the two coordinates. The rank's `Fin.isLt` proof
selects the valid branch without computing the cardinality. The inverse
law of the same explicitly instantiated equivalence recovers the table. -/
private theorem decodeOracleTable_rank (k n : ℕ) (table : CanonTab k n) :
    decodeOracleTable (Nat.pair k (Nat.pair n
      ((@Fintype.equivFin (CanonTab k n) (canonTabFintype k n)) table).val)) =
      (⟨k, Fin n, table.val, table.property⟩ : FinOracleTM Bool) := by
  simp only [decodeOracleTable, Nat.unpair_pair]
  rw [oracleTableAt, dif_pos ((@Fintype.equivFin (CanonTab k n) (canonTabFintype k n)) table).isLt]
  exact congrArg
    (fun a : CanonTab k n => (⟨k, Fin n, a.val, a.property⟩ : FinOracleTM Bool))
    ((@Fintype.equivFin (CanonTab k n) (canonTabFintype k n)).symm_apply_apply table)

/-- R5: forget the second coordinate, so every decoded table is repeated. -/
private noncomputable def oracleEnumeration (i : ℕ) : FinOracleTM Bool :=
  decodeOracleTable (Nat.unpair i).1

/-- R5: every repetition coordinate yields the same decoded table. -/
private theorem oracleEnumeration_pair (j r : ℕ) :
    oracleEnumeration (Nat.pair j r) = decodeOracleTable j := by
  simp only [oracleEnumeration, Nat.unpair_pair]

/-- **Enumeration of the deterministic finite oracle machines with infinite
recurrence** [BGS75, p. 432]: there is a family `N : ℕ → Turing.FinOracleTM
Bool` such that every finite oracle machine `M` recurs at arbitrarily late
indices, up to behavioral equality — equal `ComputesInTime` verdicts under
every oracle, at every input, output, and horizon.

The statement is deliberately *clock-free* (no `DecidesInTime`): [BGS75]
requires the enumerated machines' polynomial clocks to hold under **every**
oracle, so the stage construction supplies the budget `fun n => n ^ i + i`
extrinsically at index `i` — an explicit step count, meaningful under any
oracle — rather than reading a clock off the machine. Since every machine
recurs at arbitrarily late indices and the budgets grow with `i`, each machine
is eventually paired with every polynomial majorant (the index plays the role
of [BGS75]'s machine/clock-exponent pairing).

**Proof sketch.** For fixed tape count `k` and state count `m + 1`, the oracle
machines over `Bool` with state space `Fin (m + 1)` form a finite type (the
transition table is a function between finite types), so `Fintype.equivFin`
enumerates the well-formed ones; a pairing of `ℕ` with `ℕ × ℕ × ℕ × ℕ` —
tape count, state count, table rank, and an explicit **repetition
coordinate** (a bijective pairing alone has singleton fibers; the fourth
coordinate supplies the recurrence and the unbounded clock exponents —
round-1 finding 2) — produces the family, totalized by a fixed well-formed
**three-state** default at indices whose rank overflows (well-formedness
demands three pairwise-distinct special states, so no one-state machine
qualifies — round-1 finding 2; equivalently, embed a one-state plain
machine by `Turing.FinTM.toFinOracleTM`, which adjoins them).
Every bundled `M : Turing.FinOracleTM Bool` relabels its state type along
`Fintype.equivFin` to some `Fin (m + 1)`, preserving runs
configuration-by-configuration under every oracle — the oracle transport of
`Turing.MultiTapeTM.relabelState` / `relabelState_runFrom_init`
(`TCSlib.Complexity.TuringMachine.StateRenaming`), with the query step
commuting with the renaming because `Turing.OracleTM.queryString` ignores the
state. Fill obligations, named for the brief: the `OracleTM` relabelling lemma
(its natural home is the frozen `StateRenaming`/`Oracle` pair, so it lands in
this phase's files — flagged for promotion); transfer of `ComputesInTime`
across the configuration bijection (`Turing.Cfg.mapState` preserves
haltedness and output, as in `Turing.exists_codeTM`); the arithmetic of the
four-coordinate pairing (round-2 finding 2).

**C1d proof-sketch appendix.** Canonical tables are indexed by every state
count `n`, including the empty table types at small counts; invalid ranks
use the three-state fallback. `oracleTableAt` exposes the three coordinates
before the dependent rank branch is opened. Every table rank and cardinality
uses the one named finiteness structure. Runs follow from the single step
transport by `Function.Semiconj.iterate_right`; `Nat.right_le_pair` gives
the recurrence bound directly. -/
theorem exists_finOracleTM_enumeration :
    ∃ N : ℕ → FinOracleTM Bool,
      ∀ (M : FinOracleTM Bool) (i₀ : ℕ),
        ∃ i, i₀ ≤ i ∧
          ∀ (O : Language Bool) (x output : List Bool) (t : ℕ),
            ((N i).ComputesInTime O x output t ↔ M.ComputesInTime O x output t) := by
  refine ⟨oracleEnumeration, ?_⟩
  intro M i₀
  rcases M with @⟨k, Q, hQ, dQ, tm, wf⟩
  letI : Fintype Q := hQ
  letI : DecidableEq Q := dQ
  let e := Fintype.equivFin Q
  let table : CanonTab k (Fintype.card Q) :=
    ⟨oracleRelabel tm e, oracleRelabel_wellFormed tm e wf⟩
  let j := Nat.pair k (Nat.pair (Fintype.card Q)
    ((@Fintype.equivFin (CanonTab k (Fintype.card Q))
      (canonTabFintype k (Fintype.card Q))) table).val)
  refine ⟨Nat.pair j i₀, Nat.right_le_pair j i₀, ?_⟩
  intro O x output t
  have htable : decodeOracleTable j =
      (⟨k, Fin (Fintype.card Q), table.val, table.property⟩ : FinOracleTM Bool) :=
    decodeOracleTable_rank k (Fintype.card Q) table
  rw [oracleEnumeration_pair, htable]
  exact oracleRelabel_computesInTime tm e O x output t

/-- **Counting**: a list of fewer than `2 ^ n` words misses some word of length `n`
[AB09, proof of Theorem 3.7: polynomially many queries cannot cover all `2^n` strings].

**Proof sketch.** Otherwise `j ↦ (the `n` low bits of `j`)` would inject
`Finset.range (2 ^ n)` into the list's distinct entries (`Nat.eq_of_testBit_eq`, the bits
at positions `≥ n` vanishing below `2 ^ n`), whose number is at most its length. -/
private theorem exists_length_not_mem (n : ℕ) (Q : List (List Bool)) (hQ : Q.length < 2 ^ n) :
    ∃ z : List Bool, z.length = n ∧ z ∉ Q := by
  classical
  by_contra hcon
  push_neg at hcon
  have hle : (Finset.range (2 ^ n)).card ≤ Q.toFinset.card := by
    refine Finset.card_le_card_of_injOn (fun j => List.ofFn fun i : Fin n => j.testBit i) ?_ ?_
    · intro j _
      simpa using hcon _ List.length_ofFn
    · intro a ha b hb hab
      have ha' : a < 2 ^ n := by simpa using ha
      have hb' : b < 2 ^ n := by simpa using hb
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < n
      · have := congrArg (fun l : List Bool => l[i]?) hab
        simpa [hi] using this
      · have hn : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha' hn),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb' hn)]
  rw [Finset.card_range] at hle
  have := List.toFinset_card_le Q
  omega

/-- **A fresh stage length**: beyond any bound `b` there is a length `n ≥ i + 2` at which
the stage budget `n ^ i + i` stays below the `2 ^ n` words of length `n`.

**Proof sketch.** Take `n = 2 ^ 2 ^ m` with `m = i + b + 1`: then `n ^ i = 2 ^ (2 ^ m · i)`,
and `2 ^ m · i + 1 ≤ 2 ^ (m + i) ≤ 2 ^ 2 ^ m` because `m + i ≤ 2m ≤ 2 ^ m`, all from
`Nat.lt_two_pow_self`. -/
private theorem exists_fresh_len (i b : ℕ) :
    ∃ n, b < n ∧ i + 2 ≤ n ∧ n ^ i + i < 2 ^ n := by
  set m := i + b + 1 with hm
  have h2m : 2 * m ≤ 2 ^ m := by
    have := Nat.lt_two_pow_self (n := m - 1)
    have hm1 : m = (m - 1) + 1 := by omega
    rw [hm1, pow_succ]; omega
  have hmlt : m < 2 ^ m := Nat.lt_two_pow_self
  have hAlt : 2 ^ m < 2 ^ 2 ^ m := Nat.lt_two_pow_self
  refine ⟨2 ^ 2 ^ m, by omega, by omega, ?_⟩
  have hi : i + 1 ≤ 2 ^ i := Nat.lt_two_pow_self
  rw [← pow_mul]
  have hexp : 2 ^ m * i + 1 ≤ 2 ^ m * 2 ^ i := by
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    nlinarith
  have hexp2 : 2 ^ m * 2 ^ i ≤ 2 ^ 2 ^ m := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hsmall : i < 2 ^ (2 ^ m * i) ∨ i = 0 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact Or.inr h
    · left
      calc i < 2 ^ i := Nat.lt_two_pow_self
        _ ≤ 2 ^ (2 ^ m * i) :=
          Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_left i (by positivity))
  have hpow : 2 ^ (2 ^ m * i) * 2 ≤ 2 ^ 2 ^ 2 ^ m := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) (by omega)
  rcases hsmall with h | h
  · omega
  · subst h
    simp only [Nat.mul_zero, pow_zero, Nat.add_zero]
    exact Nat.one_lt_two_pow (by positivity)

/-- The data after a stage: the finitely many words declared in the oracle so far, and the
bound below which all lengths are decided. -/
private structure StageData where
  pos : Finset (List Bool)
  bound : ℕ

/-- The finite partial oracle of the declared words; undetermined words answer "no". -/
private def posOracle (P : Finset (List Bool)) : Language Bool := {z | z ∈ P}

/-- The chosen fresh length of stage `i` above the bound `b`. -/
private noncomputable def freshLen (i b : ℕ) : ℕ := Classical.choose (exists_fresh_len i b)

/-- The fresh length's three defining properties. -/
private theorem freshLen_spec (i b : ℕ) :
    b < freshLen i b ∧ i + 2 ≤ freshLen i b ∧ freshLen i b ^ i + i < 2 ^ freshLen i b :=
  Classical.choose_spec (exists_fresh_len i b)

/-- Stage `i`'s query list: the words that `N i` submits on `1^nᵢ` within the budget
`nᵢ ^ i + i`, run against the partial oracle. -/
private noncomputable def stageQ (N : ℕ → FinOracleTM Bool) (i : ℕ) (d : StageData) :
    List (List Bool) :=
  (N i).tm.queriesWithin (posOracle d.pos) (List.replicate (freshLen i d.bound) true)
    (freshLen i d.bound ^ i + i)

/-- Stage `i` submits fewer than `2 ^ nᵢ` queries (`queriesWithin_length_le`). -/
private theorem stageQ_length (N : ℕ → FinOracleTM Bool) (i : ℕ) (d : StageData) :
    (stageQ N i d).length < 2 ^ freshLen i d.bound :=
  (OracleTM.queriesWithin_length_le _ _ _ _).trans_lt (freshLen_spec i d.bound).2.2

/-- The unqueried witness `x⋆` of stage `i`, of length `nᵢ`. -/
private noncomputable def stageWit (N : ℕ → FinOracleTM Bool) (i : ℕ) (d : StageData) :
    List Bool :=
  Classical.choose (exists_length_not_mem _ _ (stageQ_length N i d))

/-- The witness has length `nᵢ` and is not among stage `i`'s queries. -/
private theorem stageWit_spec (N : ℕ → FinOracleTM Bool) (i : ℕ) (d : StageData) :
    (stageWit N i d).length = freshLen i d.bound ∧ stageWit N i d ∉ stageQ N i d :=
  Classical.choose_spec (exists_length_not_mem _ _ (stageQ_length N i d))

/-- Stage `i`'s run accepts: halted with output `[true]` within the budget. -/
private def StageAccepts (N : ℕ → FinOracleTM Bool) (i : ℕ) (d : StageData) : Prop :=
  (N i).ComputesInTime (posOracle d.pos) (List.replicate (freshLen i d.bound) true) [true]
    (freshLen i d.bound ^ i + i)

open Classical in
/-- **The flip** [AB09, proof of Theorem 3.7]: if stage `i`'s run accepts, declare
nothing; otherwise declare the unqueried witness. Afterwards every length up to
`max nᵢ (nᵢ ^ i + i)` is decided (the `max` matters at `i = 0`, audit test A9). -/
private noncomputable def stageStep (N : ℕ → FinOracleTM Bool) (i : ℕ) (d : StageData) :
    StageData :=
  ⟨if StageAccepts N i d then d.pos else insert (stageWit N i d) d.pos,
    max (freshLen i d.bound) (freshLen i d.bound ^ i + i)⟩

/-- The stage recursion, from the empty declaration. -/
private noncomputable def stage (N : ℕ → FinOracleTM Bool) : ℕ → StageData
  | 0 => ⟨∅, 0⟩
  | i + 1 => stageStep N i (stage N i)

/-- The oracle `B` of [AB09, Theorem 3.7]: the union of all stage declarations. -/
private def bgsOracle (N : ℕ → FinOracleTM Bool) : Language Bool :=
  {z | ∃ i, z ∈ (stage N i).pos}

/-- A stage only adds declarations. -/
private theorem stage_pos_succ (N : ℕ → FinOracleTM Bool) (i : ℕ) :
    (stage N i).pos ⊆ (stage N (i + 1)).pos := by
  classical
  show (stage N i).pos ⊆ (stageStep N i (stage N i)).pos
  unfold stageStep
  split_ifs
  · exact subset_rfl
  · exact Finset.subset_insert _ _

/-- Declarations persist through all later stages. -/
private theorem stage_pos_mono (N : ℕ → FinOracleTM Bool) {i j : ℕ} (h : i ≤ j) :
    (stage N i).pos ⊆ (stage N j).pos := by
  induction j, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ j _ ih => exact ih.trans (stage_pos_succ N j)

/-- The decided bound after stage `i`. -/
private theorem stage_bound_succ (N : ℕ → FinOracleTM Bool) (i : ℕ) :
    (stage N (i + 1)).bound =
      max (freshLen i (stage N i).bound) (freshLen i (stage N i).bound ^ i + i) := rfl

/-- Decided bounds grow along the stages. -/
private theorem stage_bound_mono (N : ℕ → FinOracleTM Bool) {i j : ℕ} (h : i ≤ j) :
    (stage N i).bound ≤ (stage N j).bound := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    rw [stage_bound_succ]
    have := (freshLen_spec j (stage N j).bound).1
    omega

/-- Every later fresh length exceeds an earlier stage's length and budget. -/
private theorem stage_later (N : ℕ → FinOracleTM Bool) {i j : ℕ} (h : i < j) :
    freshLen i (stage N i).bound ^ i + i < freshLen j (stage N j).bound ∧
      freshLen i (stage N i).bound < freshLen j (stage N j).bound := by
  have h1 := stage_bound_mono N (show i + 1 ≤ j by omega)
  rw [stage_bound_succ] at h1
  have h2 := (freshLen_spec j (stage N j).bound).1
  constructor <;> omega

/-- The only word a stage can add is its witness, and only when its run did not accept. -/
private theorem stage_new (N : ℕ → FinOracleTM Bool) (i : ℕ) {z : List Bool}
    (h₁ : z ∈ (stage N (i + 1)).pos) (h₂ : z ∉ (stage N i).pos) :
    z = stageWit N i (stage N i) ∧ ¬StageAccepts N i (stage N i) := by
  classical
  change z ∈ (stageStep N i (stage N i)).pos at h₁
  unfold stageStep at h₁
  split_ifs at h₁ with hacc
  · exact absurd h₁ h₂
  · rcases Finset.mem_insert.mp h₁ with h | h
    · exact ⟨h, hacc⟩
    · exact absurd h h₂

/-- Every word of `B` entered at some stage.

**Proof sketch.** The least stage containing it is positive (stage `0` is empty), and
the word is new there. -/
private theorem exists_entry (N : ℕ → FinOracleTM Bool) {z : List Bool}
    (hz : z ∈ bgsOracle N) :
    ∃ s, z ∈ (stage N (s + 1)).pos ∧ z ∉ (stage N s).pos := by
  classical
  have hex : ∃ j, z ∈ (stage N j).pos := hz
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · have := Nat.find_spec hex
      rw [h] at this
      exact absurd this (Finset.notMem_empty z)
    · exact h
  refine ⟨Nat.find hex - 1, ?_, Nat.find_min hex (by omega)⟩
  rw [Nat.sub_add_cancel hpos]
  exact Nat.find_spec hex

/-- Every member has the length of its entry stage. -/
private theorem entry_length (N : ℕ → FinOracleTM Bool) {z : List Bool} {s : ℕ}
    (h₁ : z ∈ (stage N (s + 1)).pos) (h₂ : z ∉ (stage N s).pos) :
    z.length = freshLen s (stage N s).bound := by
  obtain ⟨rfl, -⟩ := stage_new N s h₁ h₂
  exact (stageWit_spec N s (stage N s)).1

/-- **Consistency** [AB09, proof of Theorem 3.7]: on every word stage `i` queried, the
partial oracle and `B` agree.

**Proof sketch.** Declared words stay declared. Conversely a queried word of `B` entered
at some stage `s`: not at `s = i`, whose witness is unqueried; not at `s > i`, whose words
are longer than stage `i`'s budget, hence than any of its queries
(`length_le_of_mem_queriesWithin`); so `s < i`, and it is already declared. -/
private theorem stage_consistent (N : ℕ → FinOracleTM Bool) (i : ℕ) :
    ∀ z ∈ stageQ N i (stage N i), (z ∈ posOracle (stage N i).pos ↔ z ∈ bgsOracle N) := by
  intro z hz
  constructor
  · intro h; exact ⟨i, h⟩
  · intro hB
    obtain ⟨s, h₁, h₂⟩ := exists_entry N hB
    rcases lt_trichotomy s i with hs | rfl | hs
    · exact stage_pos_mono N (show s + 1 ≤ i by omega) h₁
    · exact absurd ((stage_new N s h₁ h₂).1 ▸ hz) (stageWit_spec N s (stage N s)).2
    · have hlen := OracleTM.length_le_of_mem_queriesWithin hz
      have hz' := entry_length N h₁ h₂
      have := (stage_later N hs).1
      omega

/-- The stage-`i` verdicts under `B` and under the partial oracle coincide: query-set
locality (`runFrom_eq_of_agree_queriesWithin`), with the partial oracle first. -/
private theorem stage_transfer (N : ℕ → FinOracleTM Bool) (i : ℕ) (out : List Bool) :
    (N i).ComputesInTime (bgsOracle N) (List.replicate (freshLen i (stage N i).bound) true) out
        (freshLen i (stage N i).bound ^ i + i) ↔
      (N i).ComputesInTime (posOracle (stage N i).pos)
        (List.replicate (freshLen i (stage N i).bound) true) out
        (freshLen i (stage N i).bound ^ i + i) := by
  have hrun := OracleTM.runFrom_eq_of_agree_queriesWithin (N i).tm (posOracle (stage N i).pos)
    (bgsOracle N) _ _ (stage_consistent N i)
  unfold FinOracleTM.ComputesInTime OracleTM.ComputesInTime
  rw [hrun]

/-- `1^n ∈ U_B` iff `B` has a word of length `n`. -/
private theorem mem_unaryWitnessLang_replicate (B : Language Bool) (n : ℕ) :
    List.replicate n true ∈ unaryWitnessLang B ↔
      ∃ y : List Bool, y.length = n ∧ y ∈ B := by
  constructor
  · rintro ⟨m, hm, y, hy, hyB⟩
    have : n = m := by simpa using congrArg List.length hm
    exact ⟨y, hy.trans this.symm, hyB⟩
  · rintro ⟨y, hy, hyB⟩
    exact ⟨n, rfl, y, hy, hyB⟩

/-- **The flipped verdict survives to `B`**: `N i` accepts `1^nᵢ` under `B` within the
stage budget iff `1^nᵢ ∉ U_B`.

**Proof sketch.** By `stage_transfer` the verdict is stage `i`'s. If it accepted, no word
of length `nᵢ` is ever declared: earlier stages declare shorter words, later stages
longer ones, and stage `i` declared nothing. If it did not, the witness of length `nᵢ` is
declared. -/
private theorem stage_flip (N : ℕ → FinOracleTM Bool) (i : ℕ) :
    (N i).ComputesInTime (bgsOracle N) (List.replicate (freshLen i (stage N i).bound) true) [true]
        (freshLen i (stage N i).bound ^ i + i) ↔
      List.replicate (freshLen i (stage N i).bound) true ∉ unaryWitnessLang (bgsOracle N) := by
  rw [stage_transfer, mem_unaryWitnessLang_replicate]
  change StageAccepts N i (stage N i) ↔ _
  constructor
  · rintro hacc ⟨y, hy, hyB⟩
    obtain ⟨s, h₁, h₂⟩ := exists_entry N hyB
    have hlen := entry_length N h₁ h₂
    rcases lt_trichotomy s i with hs | rfl | hs
    · have := (stage_later N hs).2; omega
    · exact (stage_new N s h₁ h₂).2 hacc
    · have := (stage_later N hs).2; omega
  · intro hno
    by_contra hacc
    apply hno
    refine ⟨stageWit N i (stage N i), (stageWit_spec N i (stage N i)).1, i + 1, ?_⟩
    classical
    change stageWit N i (stage N i) ∈ (stageStep N i (stage N i)).pos
    unfold stageStep
    rw [if_neg hacc]
    exact Finset.mem_insert_self _ _

/-- **Domination at late stages**: once `i ≥ k + 1 + 2c`, the stage budget exceeds
`c · (nᵢ ^ k + 1)`, since `nᵢ ≥ i + 2` gives
`c(n^k + 1) ≤ 2c · n^k ≤ n^(k+1) ≤ n^i`. -/
private theorem stage_dominates (N : ℕ → FinOracleTM Bool) (c k i : ℕ)
    (hi : k + 1 + 2 * c ≤ i) :
    c * (freshLen i (stage N i).bound ^ k + 1) ≤ freshLen i (stage N i).bound ^ i + i := by
  set n := freshLen i (stage N i).bound
  have hn : i + 2 ≤ n := (freshLen_spec i (stage N i).bound).2.1
  have hpk : 1 ≤ n ^ k := Nat.one_le_pow _ _ (by omega)
  calc c * (n ^ k + 1) ≤ c * (2 * n ^ k) := Nat.mul_le_mul_left _ (by omega)
    _ = (2 * c) * n ^ k := by ring
    _ ≤ n * n ^ k := Nat.mul_le_mul_right _ (by omega)
    _ = n ^ (k + 1) := by ring
    _ ≤ n ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ n ^ i + i := Nat.le_add_right _ _

/-- **The stage construction** [AB09, Theorem 3.7; BGS75, §3]: there is an
oracle `B` whose unary witness language lies in `NP^B` but not in `P^B`.

**Proof sketch.** Fix the enumeration `N` of
`Complexity.exists_finOracleTM_enumeration`, with the extrinsic budget
`T_i n := n ^ i + i` at index `i` ([BGS75]'s all-oracle clock, attached to the
index, never read off the machine).

*Stages.* Construct, by recursion on `i`, finite partial oracles: a finite set
of strings declared **in** `B` and a bound below which all lengths are
**decided**. At stage `i`: pick `nᵢ` exceeding every previously decided length
*and every earlier budget `nⱼ^j + j`* (so no earlier run ever queried a string
of length `≥ nᵢ`, and no later declaration can disturb an earlier answer), and
large enough that `nᵢ ^ i + i < 2 ^ nᵢ`, so the run below cannot query all
`2 ^ nᵢ` strings of length `nᵢ` (the P3.2 route's stronger margin
`2 ^ (nᵢ / 10) > nᵢ ^ i + i` is not needed). Run `N i` on input `1^nᵢ`
for exactly `nᵢ ^ i + i` steps with the partial oracle `Oᵢ` (the strings
declared in so far; every undetermined string answered "no").

*Flip.* If that run accepts — `(N i).ComputesInTime Oᵢ 1^nᵢ [true]
(nᵢ ^ i + i)` — declare every length-`nᵢ` string out of `B`, so
`1^nᵢ ∉ U_B`. Otherwise the run submitted at most `nᵢ ^ i + i` queries
(`Turing.OracleTM.queriesWithin_length_le`), each of length at most the budget
(`Turing.OracleTM.length_le_of_mem_queriesWithin`), so some length-`nᵢ` string
`x⋆` is unqueried (counting: `nᵢ ^ i + i < 2 ^ nᵢ` strings of length `nᵢ`);
declare `x⋆ ∈ B` and every other length-`nᵢ` string out, so `1^nᵢ ∈ U_B`.
In either case all lengths up to `max nᵢ (nᵢ ^ i + i)` become decided — the
`max` matters at small indices (`i = 0` has budget `1 < n₀`), where the flip
declares length-`nᵢ` strings that the budget alone would leave undecided.

*Consistency.* Let `B` be the union of the stage declarations. `B` agrees with
`Oᵢ` on every string stage `i`'s run queried: earlier declarations are
contained in `Oᵢ`; the flip inserts at most the *unqueried* `x⋆`; later stages
only insert strings longer than stage `i`'s budget, hence longer than every
stage-`i` query. By query-set locality
(`Turing.OracleTM.runFrom_eq_of_agree_queriesWithin`), the run of `N i` on
`1^nᵢ` under `B` coincides with the run under `Oᵢ` — the flipped verdict
survives to the completed oracle: for every `i`, `(N i).ComputesInTime B
1^nᵢ [true] (nᵢ ^ i + i)` holds iff `1^nᵢ ∉ U_B`.

*Conclusion.* `U_B ∈ NP^B` is `Complexity.unaryWitnessLang_mem_NPOracle`.
Suppose `U_B ∈ P^B`: some well-formed `M` decides it within `c · (n^k + 1)`.
The recurrence yields `i` with `N i` behaviorally equal to `M` and `i` so
large that `c · (nᵢ^k + 1) ≤ nᵢ ^ i + i` (the stages may also force `nᵢ ≥ i`,
absorbing the constants). `M`'s verdict on `1^nᵢ` at its clock transfers, by
monotonicity of `ComputesInTime` (halting is absorbing) and behavioral
equality, to `N i` at the budget `nᵢ ^ i + i` under `B` — contradicting the
flipped verdict in both cases (accept and reject). Fill obligations, named
for the brief: the stage recursion as a definition by strong recursion with
its monotonicity invariants (decided lengths grow, declarations are
preserved); the unqueried-string count (`Finset` cardinality of length-`nᵢ`
strings vs. the query list); the `DecidesInTime`-to-`ComputesInTime` verdict
extraction (indicator output plus `mono`); the final transfer along the
enumeration's behavioral equivalence.

**B1 appendix.** The fresh lengths and the unqueried witnesses are chosen by
`Classical.choose`; the counting is import-free (a `Nat.testBit` injection of
`Finset.range (2 ^ n)`); domination is taken at `i ≥ k + 1 + 2c` with `nᵢ ≥ i + 2`. -/
theorem exists_oracle_ne :
    ∃ B : Language Bool,
      unaryWitnessLang B ∈ NPOracle B ∧ unaryWitnessLang B ∉ POracle B := by
  classical
  obtain ⟨N, hN⟩ := exists_finOracleTM_enumeration
  refine ⟨bgsOracle N, unaryWitnessLang_mem_NPOracle _, ?_⟩
  intro hP
  obtain ⟨k, c, M, hM⟩ := Set.mem_iUnion.mp hP
  obtain ⟨i, hi, hbeh⟩ := hN M (k + 1 + 2 * c)
  set n := freshLen i (stage N i).bound
  have hdec := hM (List.replicate n true)
  simp only [List.length_replicate] at hdec
  have hlift := hdec.mono (stage_dominates N c k i hi)
  have hNi := (hbeh _ _ _ _).mpr hlift
  by_cases hx : List.replicate n true ∈ unaryWitnessLang (bgsOracle N)
  · have hacc :
        (N i).ComputesInTime (bgsOracle N) (List.replicate n true) [true] (n ^ i + i) := by
      simpa [MultiTapeTM.indicator, hx] using hNi
    exact (stage_flip N i).mp hacc hx
  · have hrej :
        (N i).ComputesInTime (bgsOracle N) (List.replicate n true) [false] (n ^ i + i) := by
      simpa [MultiTapeTM.indicator, hx] using hNi
    have hacc := (stage_flip N i).mpr hx
    exact absurd (hrej.output_unique hacc) (by simp)

/-- **The Baker-Gill-Solovay theorem** [AB09, Theorem 3.7] ([BGS75]): there
are oracles `A`, `B` with `P^A = NP^A` and `P^B ≠ NP^B` — whether `P = NP`
does not relativize.

**Proof sketch.** `A := Complexity.EXPCOM` with
`Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM`; `B` from
`Complexity.exists_oracle_ne` — were `P^B = NP^B`, its `U_B ∈ NP^B` and
`U_B ∉ P^B` would collide.

**Fill appendix (maintainer).** Exactly the sketch, as derived in
`audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`. It is proved modulo the
`EXPCOM` identity, which rests on B5's summit and `EXP ⊆ P^EXPCOM`, and modulo
`exists_uniformMachineCode` (B5a), on which the language `EXPCOM` itself rests through
`Complexity.expCode`. The `B` half (`Complexity.exists_oracle_ne`) is admission-free. -/
theorem baker_gill_solovay :
    (∃ A : Language Bool, POracle A = NPOracle A) ∧
    ∃ B : Language Bool, POracle B ≠ NPOracle B := by
  refine ⟨⟨EXPCOM, POracle_EXPCOM_eq_NPOracle_EXPCOM⟩, ?_⟩
  obtain ⟨B, h1, h2⟩ := exists_oracle_ne
  exact ⟨B, fun h => h2 (h ▸ h1)⟩

end Complexity
