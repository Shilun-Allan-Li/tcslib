/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.UniversalStartup

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Universal machine: the table interpreter

The four-tape table interpreter of the universal machine: its finite control
`UniversalControl`, the interpreter `universalInterpreter` and the complete
candidate `universalTM`, the table/state-tape gadget lemmas, exact interpreter
initialization, and the block-simulation assembly `universal_from_blocks`.
This file was split out mechanically from `Universal.lean` at the epoch-3→4
merge; its contents are the epoch-3 fill, batches B (WIP) and B2 (completion),
unchanged. The file also carries the head of the epoch-3B2 completion (the
record grammar `universal_record_shape` and the record-skipping gadgets up to
`universalSkipDone`): their proofs rely on Lean's per-module `match` auxiliary
declarations being shared with `universalRecordBits` and
`universalInterpreter`, so the module boundary sits after `universalSkipDone`.
The public surface here exists to support the epoch-4 `timed_universal` fill;
its promotion is recorded at the epoch-3→4 merge (shared-lemma requests of the
batch-B/B2 reports).

## Main definitions / Main results

* `Turing.universalInterpreter` — the fixed four-tape table interpreter.
* `Turing.universalTM` — the complete universal machine candidate.
* `Turing.universal_initialized` / `Turing.universalStartupBound` — full
  prefix-start correspondence within a suffix-independent startup bound.
* `Turing.universal_from_blocks` — assembly of both evaluator clauses from a
  configuration-level block simulation.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9, pp. 20-21.)
-/

namespace Turing

open FinTM

/-! ### The table interpreter

The four interpreter tapes are: canonical table, unary state, simulated work,
and the virtual-left-boundary marker. The state tape has a permanent `false` at
zero and the state index in unary `true`s starting at one. Each table search
consumes these unary symbols while skipping nine records per symbol. The next
state is copied from the selected record, so no code-dependent state index is
stored in finite control.
-/

/-- Finite registers and phases of the interpreter. All counters here have fixed
bounds; the unbounded simulated state is represented only on the state tape. -/
inductive UniversalControl where
  | start
  | rewindTable (initial : Bool) (index : Fin 9)
  | countFirst (initial : Bool) (index : Fin 9)
  | countSecond (initial : Bool) (index : Fin 9) (bit : Bool)
  | initialCopy
  | initialSkip (index : Fin 9)
  | rewindState (index : Option (Fin 9))
  | main
  | group (index : Fin 9)
  | skipFixed (dest : Option (Fin 9)) (remaining : Fin 9) (field : Fin 8)
  | skipUnary (dest : Option (Fin 9)) (remaining : Fin 9)
  | readAction (field : Fin 8) (bits : Fin 8 → Bool)
  | nextState (bits : Fin 8 → Bool)
  | copyState (bits : Fin 8 → Bool)
  | rewindNext (bits : Fin 8 → Bool)
  | applyRecord (bits : Fin 8 → Bool) (halt : Bool)
  | invalid
  deriving DecidableEq, Fintype

/-- Four named tape entries, without a variable-size register. -/
def universalFour {A : Type} (a b c d : A) : Fin 4 → A :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d

/-- A stationary administrative action, with explicit table and state-tape work. -/
def universalAdmin (q : UniversalControl) (table : SignType := 0)
    (state : Option (Option Bool) × SignType := (none, 0)) :
    Action 4 Bool UniversalControl :=
  ⟨0, universalFour (none, table) state (none, 0) (none, 0), none, some q⟩

/-- The three read symbols in the fixed serialization order. -/
private def universalReadIndex : Option Bool → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

/-- The record within one nine-record state block. -/
def universalRecordIndex (inp work : Option Bool) : Fin 9 :=
  ⟨3 * (universalReadIndex inp).val + (universalReadIndex work).val,
    by have hi := (universalReadIndex inp).isLt
       have hw := (universalReadIndex work).isLt
       omega⟩

/-- Decode a valid fixed two-bit head-movement field. -/
def universalSign (a b : Bool) : SignType :=
  if a then if b then .neg else .pos else .zero

/-- Decode a valid fixed two-bit optional-write field. -/
def universalWrite (a b : Bool) : Option (Option Bool) :=
  if a then some (some b) else if b then some none else none

/-- The four-tape table interpreter, with a finite control independent of the
number of coded states. Malformed administrative reads enter a live sink;
canonical-table correspondence excludes them on the inputs used by the theorem. -/
def universalInterpreter : MultiTapeTM 4 Bool UniversalControl where
  q₀ := .start
  tr := fun q inp work => match q with
    | .start =>
        ⟨0, universalFour (none, .neg) (some (some false), .pos) (none, 0)
          (some (some true), .pos), none, some (.rewindTable true 0)⟩
    | .rewindTable initial index =>
        if work 0 = none then universalAdmin (.countFirst initial index) .pos
        else universalAdmin (.rewindTable initial index) .neg
    | .countFirst initial index => match work 0 with
        | some b => universalAdmin (.countSecond initial index b) .pos
        | none => universalAdmin .invalid
    | .countSecond initial index b => match work 0 with
        | some v =>
          if b = v then universalAdmin (.countFirst initial index) .pos
          else if b = false ∧ v = true then
            universalAdmin (if initial then .initialCopy else .initialSkip index) .pos
          else universalAdmin .invalid
        | none => universalAdmin .invalid
    | .initialCopy => match work 0 with
        | some true => universalAdmin .initialCopy .pos (some (some true), .pos)
        | some false => universalAdmin (.rewindState none) .pos
        | none => universalAdmin .invalid
    | .initialSkip index => match work 0 with
        | some true => universalAdmin (.initialSkip index) .pos
        | some false => universalAdmin (.group index) .pos
        | none => universalAdmin .invalid
    | .rewindState index =>
        if work 1 = some false then
          let next := match index with
            | none => UniversalControl.main
            | some i => if h : i.val = 0 then .readAction 0 (fun _ => false)
                else .skipFixed none ⟨i.val - 1, by omega⟩ 0
          universalAdmin next 0 (none, .pos)
        else universalAdmin (.rewindState index) 0 (none, .neg)
    | .main =>
        let v := if work 3 = some true then none else inp
        universalAdmin (.rewindTable false (universalRecordIndex v (work 2))) .neg
    | .group index => match work 1 with
        | some true => universalAdmin (.skipFixed (some index) 8 0) 0 (some none, .pos)
        | none => universalAdmin (.rewindState (some index))
        | some false => universalAdmin .invalid
    | .skipFixed dest remaining field =>
        if h : field.val = 7 then universalAdmin (.skipUnary dest remaining) .pos
        else universalAdmin (.skipFixed dest remaining ⟨field.val + 1, by omega⟩) .pos
    | .skipUnary dest remaining => match work 0 with
        | some true => universalAdmin (.skipUnary dest remaining) .pos
        | some false =>
          if h : remaining.val = 0 then
            universalAdmin (match dest with
              | none => .readAction 0 (fun _ => false)
              | some i => .group i) .pos
          else universalAdmin (.skipFixed dest ⟨remaining.val - 1, by omega⟩ 0) .pos
        | none => universalAdmin .invalid
    | .readAction field bits => match work 0 with
        | some b =>
          let bs := Function.update bits field b
          if h : field.val = 7 then universalAdmin (.nextState bs) .pos
          else universalAdmin (.readAction ⟨field.val + 1, by omega⟩ bs) .pos
        | none => universalAdmin .invalid
    | .nextState bits => match work 0 with
        | some false => universalAdmin (.applyRecord bits true)
        | some true => universalAdmin (.copyState bits) .pos
        | none => universalAdmin .invalid
    | .copyState bits => match work 0 with
        | some true => universalAdmin (.copyState bits) .pos (some (some true), .pos)
        | some false => universalAdmin (.rewindNext bits)
        | none => universalAdmin .invalid
    | .rewindNext bits =>
        if work 1 = some false then universalAdmin (.applyRecord bits false) 0 (none, .pos)
        else universalAdmin (.rewindNext bits) 0 (none, .neg)
    | .applyRecord bits halt =>
        let v := if work 3 = some true then none else inp
        let d := virtualMove (decide (work 3 ≠ some true)) v (universalSign (bits 0) (bits 1))
        ⟨d, universalFour (none, 0) (none, 0)
          (universalWrite (bits 2) (bits 3), universalSign (bits 4) (bits 5)) (none, d),
          if bits 6 then some (bits 7) else none, if halt then none else some .main⟩
    | .invalid => universalAdmin .invalid

/-- State-tape representation: a permanent origin marker and a unary index. -/
def universalStateTape (q : ℕ) : ℤ → Option Bool :=
  bufferTape (false :: List.replicate q true)

/-- The complete universal machine candidate: prefix extraction and virtual
canonization, captured table, then the fixed finite table interpreter. -/
def universalTM (c : EffectiveMachineCode) : FinTM Bool :=
  universalCaptureTM (universalCanonTM c) universalInterpreter


/-- Administrative configuration with arbitrary inactive physical input, simulated
work, boundary marker, and accumulated output. Only table/state cursors vary. -/
def universalEvalCfg {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) : Cfg 4 Bool UniversalControl x :=
  { base with
    state := some q
    workTapes := universalFour (bufferTape table) state (base.workTapes 2) (base.workTapes 3)
    workTapePos := universalFour tp sp (base.workTapePos 2) (base.workTapePos 3) }

/-- The four administrative reads. -/
private lemma universalEval_reads {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) :
    (universalEvalCfg base q table tp state sp).workTapeSymbols =
      universalFour (bufferTape table tp) (state sp)
        (base.workTapeSymbols 2) (base.workTapeSymbols 3) := by
  funext i
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- One administrative action changes only the two designated tape cursors and
optionally the state-tape cell. -/
private lemma universalAdmin_apply {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q q' : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) (dt ds : SignType) (w : Option (Option Bool)) :
    (universalAdmin q' dt (w, ds)).apply (universalEvalCfg base q table tp state sp) =
      universalEvalCfg base q' table (tp + (dt : ℤ))
        (match w with | none => state | some b => Function.update state sp b)
        (sp + (ds : ℤ)) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (List.append_nil _)
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> cases w <;> rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;>
      first | rfl | exact add_zero _

/-- When the controller's transition at the represented reads (table symbol under
the cursor, state-tape symbol, and the base configuration's remaining reads)
selects the administrative action `universalAdmin q' dt (w, ds)`, one interpreter
step advances the evaluation configuration to controller state `q'`, moves the
table cursor by `dt` and the state cursor by `ds`, and performs the optional
state-tape write `w` at the old state cursor — leaving the base configuration's
other fields unchanged (epoch-4 audit, finding 2: statement prose upgraded from
the original label). -/
lemma universalEval_step {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q q' : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) (dt ds : SignType) (w : Option (Option Bool))
    (h : universalInterpreter.tr q base.inputSymbol
      (universalFour (bufferTape table tp) (state sp)
        (base.workTapeSymbols 2) (base.workTapeSymbols 3)) = universalAdmin q' dt (w, ds)) :
    universalInterpreter.step (universalEvalCfg base q table tp state sp) =
      universalEvalCfg base q' table (tp + (dt : ℤ))
        (match w with | none => state | some b => Function.update state sp b)
        (sp + (ds : ℤ)) := by
  change (universalInterpreter.tr q _ _).apply _ = _
  rw [universalEval_reads]
  change (universalInterpreter.tr q base.inputSymbol _).apply _ = _
  conv_lhs => rw [h]
  cases w <;> exact universalAdmin_apply base q q' table tp state sp dt ds _

/-- Look up the first unconsumed cell of a contiguous table. -/
lemma universal_table_read (l r : List Bool) (b : Bool) :
    bufferTape (l ++ b :: r) (l.length : ℤ) = some b := by
  rw [bufferTape_nat, List.getElem?_append_right (le_refl _)]
  simp

/-- Exact-cost table rewind. The initial unconditional left move has put the
cursor at `j-1`, where `j` is at most the table length.

**Proof sketch.** At `j=0`, the cursor is the left blank and one move right
starts the count parser. At positive `j`, a nonblank table cell is read and the
cursor decreases once. Induction accounts for every transition and leaves all
other tapes, physical input, and accumulated output unchanged. -/
lemma universal_table_rewind {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (initial : Bool) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ) :
    ∀ j, j ≤ table.length →
      universalInterpreter.runFrom
        (universalEvalCfg base (.rewindTable initial index) table (j - 1) state sp) (j + 1) =
      universalEvalCfg base (.countFirst initial index) table 0 state sp := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base (.rewindTable initial index) (.countFirst initial index)
      table (-1) state sp .pos 0 none (by simp [universalInterpreter, universalFour])
    simpa using he
  | succ j ih =>
    intro hj
    have hr : bufferTape table (j : ℤ) = some table[j] := by
      rw [bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have he := universalEval_step base (.rewindTable initial index) (.rewindTable initial index)
      table (j : ℤ) state sp .neg 0 none (by simp [universalInterpreter, universalFour, hr])
    have hh : (j + 1 : ℤ) - 1 = j := by omega
    simp only [Nat.cast_add, Nat.cast_one, hh]
    rw [he]
    simpa using ih (by omega)

/-- Skip an arbitrary doubled, delimited count field at exact cost. No binary
arithmetic on its value is needed by the interpreter.

**Proof sketch.** Each doubled pair returns the parser to its first-half state
in two transitions. The terminal aligned `false,true` pair selects the initial
state copier or skipper. Induct on the count-bit list while growing the consumed
prefix, so table lookup is justified at every cursor position. -/
lemma universal_count_run {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (initial : Bool) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (bits : List Bool) (l r : List Bool)
    (ht : table = l ++ (bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.countFirst initial index) table l.length state sp)
      (2 * bits.length + 2) =
    universalEvalCfg base (if initial then .initialCopy else .initialSkip index) table
      (l.length + 2 * bits.length + 2) state sp := by
  induction bits generalizing l with
  | nil =>
    have hr0 : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using universal_table_read l (true :: r) false
    have hr1 : bufferTape table (l.length + 1 : ℤ) = some true := by
      have h' : table = (l ++ [false]) ++ true :: r := by simp [ht, List.append_assoc]
      have h := universal_table_read (l ++ [false]) r true
      simpa [h', List.length_append] using h
    have he0 := universalEval_step base (.countFirst initial index)
      (.countSecond initial index false) table l.length state sp .pos 0 none
      (by simp [universalInterpreter, universalFour, hr0])
    have he1 := universalEval_step base (.countSecond initial index false)
      (if initial then .initialCopy else .initialSkip index)
      table (l.length + 1) state sp .pos 0 none
      (by simp [universalInterpreter, universalFour, hr1])
    change universalInterpreter.runFrom _ (0 + 1 + 1) = _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, he0]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [he1]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero,
      List.length_nil, Nat.cast_zero, mul_zero]
    congr 1
  | cons b bits ih =>
    have hr0 : bufferTape table (l.length : ℤ) = some b := by
      rw [ht]
      simpa [List.flatMap_cons, List.append_assoc] using
        universal_table_read l (b :: ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r)) b
    have hr1 : bufferTape table (l.length + 1 : ℤ) = some b := by
      have h' : table = (l ++ [b]) ++ b :: ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) := by
        simp [ht, List.append_assoc]
      have h := universal_table_read (l ++ [b]) ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) b
      simpa [h', List.length_append] using h
    have he0 := universalEval_step base (.countFirst initial index)
      (.countSecond initial index b) table l.length state sp .pos 0 none
      (by simp [universalInterpreter, universalFour, hr0])
    have he1 := universalEval_step base (.countSecond initial index b)
      (.countFirst initial index) table (l.length + 1) state sp .pos 0 none
      (by simp [universalInterpreter, universalFour, hr1])
    have h' : table = (l ++ [b, b]) ++ (bits.flatMap fun b => [b, b]) ++ [false, true] ++ r := by
      simp [ht, List.append_assoc]
    have hi := ih (l ++ [b, b]) h'
    conv_lhs => rw [show 2 * (b :: bits).length + 2 =
      1 + 1 + (2 * bits.length + 2) by simp; omega]
    rw [MultiTapeTM.runFrom_add]
    change universalInterpreter.runFrom
      (universalInterpreter.step (universalInterpreter.step _)) _ = _
    rw [he0]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [he1]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert hi using 1 <;> simp [List.length_append, List.length_cons] <;> congr 1 <;> omega


/-- State representation during destructive lookup: the first `consumed` unary
cells have been erased; `remaining` ones follow them. The origin marker persists. -/
def universalStateWindow (consumed remaining : ℕ) (z : ℤ) : Option Bool :=
  if z = 0 then some false
  else if (consumed : ℤ) < z ∧ z ≤ consumed + remaining then some true else none

/-- The intact state window is exactly the unary state-tape representation. -/
lemma universalStateWindow_zero (n : ℕ) :
    universalStateWindow 0 n = universalStateTape n := by
  funext z
  by_cases h0 : z = 0
  · subst z; simp [universalStateWindow, universalStateTape, bufferTape]
  · by_cases hz : 0 ≤ z
    · have hp : 0 < z := by omega
      have he : z.toNat = (z.toNat - 1) + 1 := by omega
      simp only [universalStateWindow, if_neg h0, Nat.cast_zero, zero_add,
        universalStateTape, bufferTape, if_pos hz]
      rw [he, List.getElem?_cons_succ]
      by_cases h : z ≤ n
      · rw [if_pos (by omega), List.getElem?_replicate_of_lt (by omega)]
      · rw [if_neg (by omega), List.getElem?_eq_none (by simp; omega)]
    · simp [universalStateWindow, universalStateTape, bufferTape, h0, hz]
      omega

/-- At the current state cursor, a nonempty window reads one. -/
lemma universalStateWindow_read (j n : ℕ) :
    universalStateWindow j (n + 1) (j + 1) = some true := by
  simp [universalStateWindow]
  omega

/-- The cursor following the erased state reads blank. -/
lemma universalStateWindow_end (j : ℕ) :
    universalStateWindow j 0 (j + 1) = none := by
  simp [universalStateWindow]
  omega

/-- Erasing one unary symbol advances the consumed prefix exactly once. -/
lemma universalStateWindow_erase (j n : ℕ) :
    Function.update (universalStateWindow j (n + 1)) (j + 1 : ℤ) none =
      universalStateWindow (j + 1) n := by
  funext z
  by_cases he : z = j + 1
  · subst z
    simp [universalStateWindow]
    omega
  · rw [Function.update_of_ne he]
    unfold universalStateWindow
    by_cases h0 : z = 0
    · simp [h0]
    · rw [if_neg h0, if_neg h0]
      simp only [Nat.cast_add, Nat.cast_one]
      split <;> split <;> first | rfl | omega

/-- A fully consumed window contains only the permanent marker, regardless of
how many symbols were erased. -/
lemma universalStateWindow_empty (j : ℕ) :
    universalStateWindow j 0 = universalStateWindow 0 0 := by
  funext z
  simp only [universalStateWindow, Nat.cast_zero, add_zero, zero_add]
  have h₁ : ¬((j : ℤ) < z ∧ z ≤ j) := by omega
  have h₂ : ¬(0 < z ∧ z ≤ 0) := by omega
  simp [h₁, h₂]

/-- Appending a next-state unary symbol extends the intact state tape. -/
private lemma universalStateTape_append (n : ℕ) :
    Function.update (universalStateTape n) (n + 1 : ℤ) (some true) =
      universalStateTape (n + 1) := by
  have h := bufferTape_append (false :: List.replicate n true) true
  simpa only [universalStateTape, List.replicate_add, List.replicate_one,
    List.cons_append, List.length_cons, List.length_replicate,
    Nat.cast_add, Nat.cast_one] using h.symm

/-- An intact unary state reads its blank immediately after the last symbol. -/
private lemma universalStateTape_end (n : ℕ) :
    universalStateTape n (n + 1) = none := by
  simp [universalStateTape, bufferTape]

/-- A marker-directed state rewind has exact cost equal to cursor plus one.
Its premise is deliberately independent of whether traversed cells are erased
blanks or retained unary ones.

**Proof sketch.** Each positive cursor sees a non-marker cell and moves left.
At zero the permanent marker causes one right move and transfer to the supplied
continuation. The entire tape, input head, and real output stay unchanged. -/
lemma universal_state_rewind {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (q q' : UniversalControl)
    (table : List Bool) (tp : ℤ) (state : ℤ → Option Bool)
    (hzero : state 0 = some false)
    (hother : ∀ j : ℕ, 0 < j → state j ≠ some false)
    (hstop : ∀ inp work, work 1 = some false →
      universalInterpreter.tr q inp work = universalAdmin q' 0 (none, .pos))
    (hscan : ∀ inp work, work 1 ≠ some false →
      universalInterpreter.tr q inp work = universalAdmin q 0 (none, .neg)) :
    ∀ j : ℕ, universalInterpreter.runFrom
      (universalEvalCfg base q table tp state j) (j + 1) =
      universalEvalCfg base q' table tp state 1 := by
  intro j
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base q q' table tp state 0 0 .pos none
      (hstop _ _ (by simpa [universalFour] using hzero))
    simpa using he
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have he := universalEval_step base q q table tp state (j + 1) 0 .neg none
      (hscan _ _ (by simpa [universalFour] using hother (j + 1) (by omega)))
    rw [show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 by omega, he]
    simpa using ih

/-- The table's initial-state unary field can be skipped at exact cost. -/
lemma universal_initial_skip {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (n : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.initialSkip index) table l.length state sp) (n + 1) =
      universalEvalCfg base (.group index) table (l.length + n + 1) state sp := by
  induction n generalizing l with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using universal_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base (.initialSkip index) (.group index)
      table l.length state sp .pos 0 none (by simp [universalInterpreter, universalFour, hr])
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        universal_table_read l (List.replicate n true ++ false :: r) true
    have he := universalEval_step base (.initialSkip index) (.initialSkip index)
      table l.length state sp .pos 0 none (by simp [universalInterpreter, universalFour, hr])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    have hi := ih (l ++ [true]) ht'
    convert hi using 1 <;> simp [List.length_append, List.length_cons] <;> congr 1 <;> omega



/-- Copy a unary table field onto the state tape. This single gadget serves both
initial-state extraction and live successor-state replacement.

**Proof sketch.** A `true` table cell appends one unary state symbol and moves both
cursors right. A terminal `false` switches to the supplied continuation, with its
specified table movement. Induction preserves exact table/state positions and
accounts for all `n+1` transitions. -/
lemma universal_unary_copy {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (q q' : UniversalControl) (doneMove : SignType)
    (table : List Bool)
    (htrue : ∀ inp work, work 0 = some true →
      universalInterpreter.tr q inp work = universalAdmin q .pos (some (some true), .pos))
    (hfalse : ∀ inp work, work 0 = some false →
      universalInterpreter.tr q inp work = universalAdmin q' doneMove (none, 0))
    (n j : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    universalInterpreter.runFrom
      (universalEvalCfg base q table l.length (universalStateTape j) (j + 1)) (n + 1) =
      universalEvalCfg base q' table (l.length + n + (doneMove : ℤ))
        (universalStateTape (j + n)) (j + n + 1) := by
  induction n generalizing l j with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using universal_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base q q' table l.length (universalStateTape j) (j + 1)
      doneMove 0 none (hfalse _ _ (by simp [universalFour, hr]))
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        universal_table_read l (List.replicate n true ++ false :: r) true
    have he := universalEval_step base q q table l.length (universalStateTape j) (j + 1)
      .pos .pos (some (some true)) (htrue _ _ (by simp [universalFour, hr]))
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, universalStateTape_append]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    have hi := ih (j + 1) (l ++ [true]) ht'
    convert hi using 1 <;> simp [List.length_append, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 n, Int.add_assoc] <;> congr 1 <;> omega

/-- The initial state tape has a unique `false` marker at zero. -/
lemma universalStateTape_marker (n : ℕ) :
    universalStateTape n 0 = some false ∧
      ∀ j : ℕ, 0 < j → universalStateTape n j ≠ some false := by
  rw [← universalStateWindow_zero]
  constructor
  · simp [universalStateWindow]
  · intro j hj
    simp only [universalStateWindow, Nat.cast_zero, zero_add]
    rw [if_neg (by omega)]
    split <;> simp

/-- Installing a single permanent marker in an otherwise blank tape. -/
private lemma universal_install_marker (b : Bool) :
    Function.update (fun _ : ℤ => none) 0 (some b) = bufferTape [b] := by
  simpa using (bufferTape_append [] b).symm

/-- Interpreter entry with the captured table on its right blank and three
fresh auxiliary tapes. Physical input is already parked at the suffix start. -/
private def universalInterpreterInitial {x : List Bool} (p : Fin (x.length + 2))
    (table : List Bool) : Cfg 4 Bool UniversalControl x :=
  ⟨some .start, p, universalFour (bufferTape table) (fun _ => none) (fun _ => none)
      (fun _ => none), universalFour table.length 0 0 0, []⟩

/-- Inactive data during interpreter initialization: physical input is stationary,
simulated work is blank, and the virtual-left marker is installed at zero with
its head at one (also for empty suffixes). -/
private def universalInterpreterBase {x : List Bool} (p : Fin (x.length + 2)) :
    Cfg 4 Bool UniversalControl x :=
  ⟨some .main, p, universalFour (fun _ => none) (fun _ => none) (fun _ => none)
      (bufferTape [true]), universalFour 0 0 0 1, []⟩

/-- The first interpreter step installs the permanent markers and starts the
unconditional table rewind. -/
private lemma universalInterpreter_first {x : List Bool} (p : Fin (x.length + 2))
    (table : List Bool) :
    universalInterpreter.step (universalInterpreterInitial p table) =
      universalEvalCfg (universalInterpreterBase p) (.rewindTable true 0) table
        (table.length - 1) (universalStateTape 0) 1 := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · rfl
    · exact universal_install_marker false
    · rfl
    · exact universal_install_marker true
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- The transition-record grammar exposed locally for interpreter proofs. This
is definitionally the serialization field dictionary from `Encoding.lean`. -/
def universalRecordBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) : List Bool :=
  (match a.inputTape with
    | .neg => [true, true] | .zero => [false, false] | .pos => [true, false]) ++
  (match (a.workTapes 0).1 with
    | none => [false, false] | some none => [false, true]
    | some (some false) => [true, false] | some (some true) => [true, true]) ++
  (match (a.workTapes 0).2 with
    | .neg => [true, true] | .zero => [false, false] | .pos => [true, false]) ++
  (match a.output with
    | none => [false, false] | some false => [true, false] | some true => [true, true]) ++
  (match a.state with
    | none => [false] | some q => true :: (List.replicate q.val true ++ [false]))

/-- Canonical record order, including all nine read pairs at every live state. -/
def universalRecords (M : CodeTM) : List Bool :=
  (List.finRange (M.numStates + 1)).flatMap fun q =>
    ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun work =>
        universalRecordBits (M.tm.tr q inp (fun _ => work))

/-- The canonical serialization begins with exactly its count field and initial
unary state; the remainder is the transition table. -/
lemma universal_serialization_header (M : CodeTM) :
    ∃ records, M.serialize =
      pairEncode (Nat.bits M.numStates) (List.replicate M.tm.q₀.val true ++ false :: records) := by
  refine ⟨universalRecords M, ?_⟩
  unfold CodeTM.serialize
  change pairEncode _ ((List.replicate M.tm.q₀.val true ++ [false]) ++ _) = _
  rw [List.append_assoc]
  apply congrArg (pairEncode (Nat.bits M.numStates))
  apply congrArg (fun r : List Bool => List.replicate M.tm.q₀.val true ++ false :: r)
  unfold universalRecords
  dsimp only [List.append]
  congr 1
  funext q
  congr 1
  funext inp
  congr 1
  funext work
  generalize M.tm.tr q inp (fun _ => work) = a
  rcases a with ⟨di, tapes, out, next⟩
  have htapes : tapes = fun _ => tapes 0 := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    rw [hi]
  rw [htapes]
  generalize tapes 0 = entry
  rcases entry with ⟨write, dm⟩
  cases di <;> cases dm <;> rcases write with _ | (_ | (_ | _)) <;>
    rcases out with _ | (_ | _) <;> cases next <;> rfl

/-- Exact interpreter initialization for a canonical count/initial-state prefix.
No transition-table lookup is involved yet.

**Proof sketch.** Install both markers (one transition), rewind the whole captured
table (`|table|+1`), skip the doubled count (`2|bits|+2`), copy the initial unary
state (`n+1`), and rewind its cursor (`n+2`). The sum is
`|table| + 2|bits| + 2n + 7`. Every intermediate configuration keeps the physical
input fixed and real output empty. -/
private lemma universalInterpreter_initialize {x : List Bool}
    (p : Fin (x.length + 2)) (table bits records : List Bool) (n : ℕ)
    (ht : table = pairEncode bits (List.replicate n true ++ false :: records)) :
    universalInterpreter.runFrom (universalInterpreterInitial p table)
      (table.length + 2 * bits.length + 2 * n + 7) =
    universalEvalCfg (universalInterpreterBase p) .main table
      (2 * bits.length + 2 + n + 1) (universalStateTape n) 1 := by
  let base := universalInterpreterBase p
  have hrew := universal_table_rewind base true 0 table (universalStateTape 0) 1
    table.length (le_refl _)
  have hcount := universal_count_run base true 0 table (universalStateTape 0) 1
    bits [] (List.replicate n true ++ false :: records) (by simpa [pairEncode] using ht)
  let countPrefix := (bits.flatMap fun b => [b, b]) ++ [false, true]
  have hlen : countPrefix.length = 2 * bits.length + 2 := by
    simpa [countPrefix, pairEncode] using universal_pair_length bits []
  have hcopy := universal_unary_copy base .initialCopy (.rewindState none) .pos table
    (by intro inp work h; simp [universalInterpreter, h])
    (by intro inp work h; simp [universalInterpreter, h]) n 0 countPrefix records
    (by simpa [countPrefix, pairEncode, List.append_assoc] using ht)
  have hstate := universal_state_rewind base (.rewindState none) .main table
    (2 * bits.length + 2 + n + 1) (universalStateTape n)
    (universalStateTape_marker n).1 (universalStateTape_marker n).2
    (by intro inp work h; simp [universalInterpreter, h])
    (by intro inp work h; simp [universalInterpreter, h]) (n + 1)
  have htime : table.length + 2 * bits.length + 2 * n + 7 =
      1 + (table.length + 1) + (2 * bits.length + 2) + (n + 1) + (n + 2) := by omega
  rw [htime,
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1) + (2 * bits.length + 2) + (n + 1)) (n + 2),
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1) + (2 * bits.length + 2)) (n + 1),
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1)) (2 * bits.length + 2),
    MultiTapeTM.runFrom_add _ 1 (table.length + 1)]
  change universalInterpreter.runFrom
    (universalInterpreter.runFrom
      (universalInterpreter.runFrom
        (universalInterpreter.runFrom
          (universalInterpreter.step (universalInterpreterInitial p table))
          (table.length + 1)) (2 * bits.length + 2)) (n + 1)) (n + 2) = _
  rw [universalInterpreter_first, hrew]
  have hc : universalInterpreter.runFrom
      (universalEvalCfg base (.countFirst true 0) table 0 (universalStateTape 0) 1)
      (2 * bits.length + 2) =
    universalEvalCfg base .initialCopy table (2 * bits.length + 2) (universalStateTape 0) 1 := by
    simpa using hcount
  rw [hc]
  have hp : universalInterpreter.runFrom
      (universalEvalCfg base .initialCopy table (2 * bits.length + 2) (universalStateTape 0) 1)
      (n + 1) =
    universalEvalCfg base (.rewindState none) table (2 * bits.length + 2 + n + 1)
      (universalStateTape n) (n + 1) := by
    simpa [hlen] using hcopy
  rw [hp]
  simpa using hstate


/-- Source configurations represented at interpreter checkpoints. The table
cursor is the only administrative coordinate left unspecified by the source. -/
def universalSimulationCfg (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (tablePos : ℕ) :
    Cfg 4 Bool UniversalControl (pairEncode α x) :=
  ⟨src.state.map (fun _ => .main), universalInputPos α x src.inputPos,
    universalFour (bufferTape M.serialize)
      (universalStateTape ((src.state.map Fin.val).getD 0)) (src.workTapes 0)
      (bufferTape [true]), universalFour tablePos 1 (src.workTapePos 0) src.inputPos.val,
    src.output⟩

/-- Checkpoint representations preserve completed-output and halting fields. -/
private lemma universalSimulation_fields (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (tablePos : ℕ) :
    ((universalSimulationCfg M α src tablePos).state = none ↔ src.state = none) ∧
      (universalSimulationCfg M α src tablePos).output = src.output := by
  simp [universalSimulationCfg]

/-- The capture-stage endpoint is precisely a right-block interpreter entry,
with the canonizer work tapes retained as inactive data. -/
private lemma universalCaptured_right {S : Type} [Fintype S] [DecidableEq S]
    (M : FinTM Bool) (D : MultiTapeTM 4 Bool S) {x : List Bool}
    (src : Cfg M.k Bool M.State x) :
    universalCapturedCfg M D src =
    rightCfg Sum.inr
      (⟨some D.q₀, src.inputPos,
        universalFour (bufferTape src.output) (fun _ => none) (fun _ => none) (fun _ => none),
        universalFour src.output.length 0 0 0, []⟩ : Cfg 4 Bool S x)
      src.workTapes src.workTapePos := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [universalCapturedCfg, universalCaptureCfg, rightCfg, tapeBlocks]
    · intro j
      rcases j with ⟨j, hj⟩
      have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;>
        simp [universalCapturedCfg, universalCaptureCfg, rightCfg, tapeBlocks, universalFour] <;> rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [universalCapturedCfg, universalCaptureCfg, rightCfg, tapeBlocks]
    · intro j
      rcases j with ⟨j, hj⟩
      have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;>
        simp [universalCapturedCfg, universalCaptureCfg, rightCfg, tapeBlocks, universalFour] <;> rfl

/-- Every interpreter run lifts to the complete capture machine without touching
its inactive prefix/canonizer work tapes. -/
lemma universalCapture_interpreter_run (M : FinTM Bool) {x : List Bool}
    (cfg : Cfg 4 Bool UniversalControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) (t : ℕ) :
    (universalCaptureTM M universalInterpreter).tm.runFrom
      (rightCfg Sum.inr cfg tapes heads) t =
    rightCfg Sum.inr (universalInterpreter.runFrom cfg t) tapes heads :=
  rightCfg_run universalInterpreter (universalCaptureTM M universalInterpreter).tm
    Sum.inr (by intros; rfl) cfg tapes heads t

/-- The code-dependent startup bound, including complete interpreter setup. -/
def universalStartupBound (c : EffectiveMachineCode) (α : List Bool) : ℕ :=
  3 * α.length + c.canonizerTime α.length + (c.decode α).serialize.length +
    2 * (Nat.bits (c.decode α).numStates).length + 2 * (c.decode α).tm.q₀.val + 12

/-- Full prefix-start correspondence: the complete candidate reaches the first
source checkpoint, with the canonical table, unary initial state, blank simulated
work tape, and virtual input marker, within a bound independent of the suffix.

**Proof sketch.** First capture the virtually run canonizer, preserving its exact
parked physical head. Identify this endpoint with a right-block interpreter entry,
then lift the exact interpreter-initialization run. The initial marker head at one
matches the native initial input position, also on empty input. No step of startup
needs the suffix length or a suffix read. -/
lemma universal_initialized (c : EffectiveMachineCode) (α x : List Bool) :
    ∃ (t : ℕ) (tapes : Fin (universalCanonTM c).k → ℤ → Option Bool)
      (heads : Fin (universalCanonTM c).k → ℤ),
      t ≤ universalStartupBound c α ∧
      (universalTM c).tm.runFrom ((universalTM c).tm.initCfg (pairEncode α x)) t =
        rightCfg Sum.inr
          (universalSimulationCfg (c.decode α) α ((c.decode α).tm.initCfg x)
            (2 * (Nat.bits (c.decode α).numStates).length + 2 + (c.decode α).tm.q₀.val + 1))
          tapes heads := by
  let T := 3 * α.length + 4 + c.canonizerTime α.length
  let src := (universalCanonTM c).tm.runFrom
    ((universalCanonTM c).tm.initCfg (pairEncode α x)) T
  have hc := universalCanon_complete c α x
  obtain ⟨t, ht, he⟩ := universalCapture_start (universalCanonTM c) universalInterpreter
    (pairEncode α x) T hc.1
  obtain ⟨records, hrecords⟩ := universal_serialization_header (c.decode α)
  have hinit := universalInterpreter_initialize src.inputPos (c.decode α).serialize
    (Nat.bits (c.decode α).numStates) records (c.decode α).tm.q₀.val hrecords
  let d := (c.decode α).serialize.length + 2 * (Nat.bits (c.decode α).numStates).length +
    2 * (c.decode α).tm.q₀.val + 7
  refine ⟨t + d, src.workTapes, src.workTapePos, ?_, ?_⟩
  · dsimp only [universalStartupBound, d, T] at *
    omega
  · change (universalCaptureTM (universalCanonTM c) universalInterpreter).tm.runFrom _ _ = _
    rw [MultiTapeTM.runFrom_add, he, universalCaptured_right]
    change (universalCaptureTM (universalCanonTM c) universalInterpreter).tm.runFrom
      (rightCfg Sum.inr (universalInterpreterInitial src.inputPos src.output)
        src.workTapes src.workTapePos) d = _
    have ho : src.output = (c.decode α).serialize := hc.2.1
    rw [ho, universalCapture_interpreter_run, hinit]
    congr 1
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      exact hc.2.2
    · funext i
      rcases i with ⟨i, hi⟩
      have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    · funext i
      rcases i with ⟨i, hi⟩
      have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;> simp [universalEvalCfg,
        universalInterpreterBase, universalSimulationCfg, universalFour, Nat.cast_add]
    · rfl

/-- A block simulation with positive block lengths gives a cofinal physical run.
The upper bound accounts for startup and each source transition; the lower bound
is what makes the completed-output converse independent of administrative phases.

**Proof sketch.** Induct on source time. Startup supplies the initial related
configuration. Append the positive-duration block for each source transition and
use run addition to concatenate it. Add the upper bounds and use positivity for
the lower bound, without assuming that source or target eventually halts. -/
private lemma universal_block_run {k l : ℕ} {Q R : Type} {x y : List Bool}
    (M : MultiTapeTM k Bool Q) (U : MultiTapeTM l Bool R)
    (relation : Cfg k Bool Q x → Cfg l Bool R y → Prop) (S B : ℕ)
    (hstart : ∃ t, t ≤ S ∧ relation (M.initCfg x) (U.runFrom (U.initCfg y) t))
    (hstep : ∀ src dst, relation src dst →
      ∃ d, 1 ≤ d ∧ d ≤ B ∧ relation (M.step src) (U.runFrom dst d)) :
    ∀ n, ∃ t, n ≤ t ∧ t ≤ S + B * n ∧
      relation (M.runFrom (M.initCfg x) n) (U.runFrom (U.initCfg y) t) := by
  intro n
  induction n with
  | zero =>
    obtain ⟨t, ht, hr⟩ := hstart
    exact ⟨t, Nat.zero_le _, by simpa using ht, hr⟩
  | succ n ih =>
    obtain ⟨t, hnt, ht, hr⟩ := ih
    obtain ⟨d, hd, hBd, hrel⟩ := hstep _ _ hr
    refine ⟨t + d, by omega, ?_, ?_⟩
    · rw [Nat.mul_succ]
      omega
    · rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add]
      exact hrel

/-- Assembly of both evaluator clauses from a configuration-level block
simulation. This lemma has no admitted premise: its simulation obligations are
explicit hypotheses that the concrete interpreter must discharge.

**Proof sketch.** In the forward direction, the cofinal block run gives a related
halted configuration by startup plus at most one block bound per source step;
`S+B` absorbs this into `(S+B)(t+1)`. For the converse, if the target has halted by
physical time `t`, take the related checkpoint after `t` source steps. Its physical
time is at least `t`, so absorbing halting preserves the completed output there.
The state/output correspondence then forces source halting with that same output.
This rules out target halting on every divergent source run, even if either run
has emitted a nonempty intermediate output. -/
lemma universal_from_blocks (c : EffectiveMachineCode) (U : FinTM Bool)
    (S B : List Bool → ℕ)
    (relation : ∀ α x : List Bool,
      Cfg 1 Bool (Fin ((c.decode α).numStates + 1)) x →
      Cfg U.k Bool U.State (pairEncode α x) → Prop)
    (hstart : ∀ α x, ∃ t, t ≤ S α ∧
      relation α x ((c.decode α).tm.initCfg x)
        (U.tm.runFrom (U.tm.initCfg (pairEncode α x)) t))
    (hstep : ∀ α x src dst, relation α x src dst →
      ∃ d, 1 ≤ d ∧ d ≤ B α ∧
        relation α x ((c.decode α).tm.step src) (U.tm.runFrom dst d))
    (hhalt : ∀ α x src dst, relation α x src dst → (src.state = none ↔ dst.state = none))
    (hout : ∀ α x src dst, relation α x src dst → src.output = dst.output) :
    ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      (∀ output : List Bool,
        (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (c.decode α).toFinTM.ComputesInTime x output t) := by
  intro α
  refine ⟨S α + B α, fun x => ?_⟩
  have hrun := universal_block_run (c.decode α).tm U.tm (relation α x)
    (S α) (B α) (hstart α x) (hstep α x)
  constructor
  · intro output t hm
    obtain ⟨v, -, hv, hr⟩ := hrun t
    have hs := (computesInTime_iff _ _ _ _).mp hm
    have hu : U.ComputesInTime (pairEncode α x) output v :=
      (computesInTime_iff _ _ _ _).mpr
        ⟨(hhalt α x _ _ hr).mp hs.1, (hout α x _ _ hr).symm.trans hs.2⟩
    apply hu.mono
    calc
      v ≤ S α + B α * t := hv
      _ ≤ S α * (t + 1) + B α * (t + 1) := by
        apply Nat.add_le_add
        · simpa only [Nat.mul_one] using Nat.mul_le_mul_left (S α) (Nat.succ_pos t)
        · exact Nat.mul_le_mul_left (B α) (by omega)
      _ = (S α + B α) * (t + 1) := by ring
  · intro output ⟨t, hu⟩
    obtain ⟨v, htv, -, hr⟩ := hrun t
    have hs := (computesInTime_iff _ _ _ _).mp (hu.mono htv)
    refine ⟨t, (computesInTime_iff _ _ _ _).mpr ?_⟩
    exact ⟨(hhalt α x _ _ hr).mpr hs.1, (hout α x _ _ hr).trans hs.2⟩


/-! ### Completion of the live table block (epoch 3B2)

The following lemmas execute the existing controller. List prefixes describe
table positions; their lengths account for every record-scanning transition.
-/

/-- The eight fixed action bits, in the order used by the canonical grammar. -/
def universalActionBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    Fin 8 → Bool :=
  fun i => match i.val with
    | 0 => decide (a.inputTape ≠ 0)
    | 1 => decide (a.inputTape = .neg)
    | 2 => match (a.workTapes 0).1 with | some (some _) => true | _ => false
    | 3 => match (a.workTapes 0).1 with | none => false | some none => true | some (some b) => b
    | 4 => decide ((a.workTapes 0).2 ≠ 0)
    | 5 => decide ((a.workTapes 0).2 = .neg)
    | 6 => a.output.isSome
    | _ => a.output.getD false

/-- Number of ones in the optional successor field, including its live flag. -/
def universalNextOnes {n : ℕ} : Option (Fin (n + 1)) → ℕ
  | none => 0
  | some q => q.val + 1

/-- Fixed fields followed by one self-delimiting unary field form a record. -/
lemma universal_record_shape {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    universalRecordBits a = List.ofFn (universalActionBits a) ++
      List.replicate (universalNextOnes a.state) true ++ [false] := by
  have hi : (match a.inputTape with
      | .neg => [true, true] | .zero => [false, false] | .pos => [true, false]) =
      [universalActionBits a 0, universalActionBits a 1] := by
    simp only [universalActionBits]
    cases a.inputTape <;> rfl
  have hw : (match (a.workTapes 0).1 with
      | none => [false, false] | some none => [false, true]
      | some (some false) => [true, false] | some (some true) => [true, true]) =
      [universalActionBits a 2, universalActionBits a 3] := by
    simp only [universalActionBits]
    rcases (a.workTapes 0).1 with _ | (_ | (_ | _)) <;> rfl
  have hm : (match (a.workTapes 0).2 with
      | .neg => [true, true] | .zero => [false, false] | .pos => [true, false]) =
      [universalActionBits a 4, universalActionBits a 5] := by
    simp only [universalActionBits]
    cases (a.workTapes 0).2 <;> rfl
  have ho : (match a.output with
      | none => [false, false] | some false => [true, false] | some true => [true, true]) =
      [universalActionBits a 6, universalActionBits a 7] := by
    simp only [universalActionBits]
    rcases a.output with _ | (_ | _) <;> rfl
  unfold universalRecordBits
  rw [hi, hw, hm, ho]
  cases a.state <;> simp only [universalNextOnes, List.replicate_succ, List.ofFn_succ] <;> rfl

/-- Skip the remaining fixed action fields, one transition per bit.

**Proof sketch.** Descending induction on the number of fields still to skip.
The last field enters the unary scanner; every other field increments the
bounded field register. No tape content is inspected or modified. -/
lemma universal_skip_fixed {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ) :
    ∀ (n : ℕ) (field : Fin 8) (tp : ℤ), field.val + n = 7 →
      universalInterpreter.runFrom
        (universalEvalCfg base (.skipFixed dest rem field) table tp state sp) (n + 1) =
      universalEvalCfg base (.skipUnary dest rem) table (tp + n + 1) state sp := by
  intro n
  induction n with
  | zero =>
    intro field tp hf
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base (.skipFixed dest rem field) (.skipUnary dest rem)
      table tp state sp .pos 0 none (by simp [universalInterpreter, show field.val = 7 by omega])
    simpa using he
  | succ n ih =>
    intro field tp hf
    have hne : field.val ≠ 7 := by omega
    have he := universalEval_step base (.skipFixed dest rem field)
      (.skipFixed dest rem ⟨field.val + 1, by omega⟩) table tp state sp .pos 0 none
      (by simp [universalInterpreter, hne])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert ih ⟨field.val + 1, by omega⟩ (tp + 1) (by simp; omega) using 1 <;>
      push_cast <;> congr 1 <;> omega

/-- Continuation after the last record in a skip request. -/
def universalSkipDone (dest : Option (Fin 9)) : UniversalControl :=
  match dest with | none => .readAction 0 (fun _ => false) | some i => .group i

end Turing
