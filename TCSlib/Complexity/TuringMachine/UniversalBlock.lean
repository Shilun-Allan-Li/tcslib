/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.UniversalInterpreter

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Universal machine: the live table block

Completion of the live serialized-table block (epoch 3B2): exact record
selection over the serialized table, fixed-field reads, successor preparation,
record application, the resulting one-source-step block
`universal_live_block`, and the concrete checkpoint relation
`universalRelation` with its start/halt/output lemmas and the block budget
`universalBlockBound`. This file was split out mechanically from
`Universal.lean` at the epoch-3→4 merge; its contents are the epoch-3 fill,
batches B (WIP) and B2 (completion), unchanged. The head of the 3B2 section
(through `universalSkipDone`) lives at the end of `UniversalInterpreter.lean`,
whose module docstring records why. The public surface here exists to support
the epoch-4 `timed_universal` fill; its promotion is recorded at the epoch-3→4
merge (shared-lemma requests of the batch-B/B2 reports).

## Main definitions / Main results

* `Turing.universal_live_block` — one live source transition is realized by
  the interpreter within the code-dependent block bound.
* `Turing.universalRelation` — the concrete checkpoint relation between source
  and universal-machine configurations.
* `Turing.universalRelation_start` / `Turing.universalRelation_halt` /
  `Turing.universalRelation_output` — the relation's startup, halting, and
  output correspondence.
* `Turing.universalBlockBound` — the code-dependent block budget.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9, pp. 20-21.)
-/

namespace Turing

open FinTM

/-- The unary tail of a skipped record costs exactly its serialized length.

**Proof sketch.** A true cell advances once without changing control. The false
terminator either finishes the request or decrements the bounded record counter.
Induction grows the consumed list prefix by one cell. -/
private lemma universal_skip_unary {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (n : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.skipUnary dest rem) table l.length state sp) (n + 1) =
    universalEvalCfg base
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table (l.length + n + 1) state sp := by
  induction n generalizing l with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using universal_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base (.skipUnary dest rem)
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table l.length state sp .pos 0 none
      (by
        by_cases h : rem.val = 0
        · have hz : rem = 0 := Fin.ext h
          simp [universalInterpreter, universalFour, hr, hz, universalSkipDone]
        · have hz : rem ≠ 0 := fun he => h (congrArg Fin.val he)
          simp [universalInterpreter, universalFour, hr, h, hz, universalSkipDone])
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        universal_table_read l (List.replicate n true ++ false :: r) true
    have he := universalEval_step base (.skipUnary dest rem) (.skipUnary dest rem)
      table l.length state sp .pos 0 none
      (by simp [universalInterpreter, universalFour, hr])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    convert ih (l ++ [true]) ht' using 1 <;>
      simp [List.length_append, List.length_cons] <;> congr 1 <;> omega

/-- Skip one complete serialized record at exact cost.

**Proof sketch.** Concatenate the eight fixed-field transitions and the unary
tail scan. The record grammar identifies their total with the record length. -/
private lemma universal_skip_record {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (a : Action 1 Bool (Fin (n + 1))) (l r : List Bool)
    (ht : table = l ++ universalRecordBits a ++ r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp)
      (universalRecordBits a).length =
    universalEvalCfg base
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table (l.length + (universalRecordBits a).length) state sp := by
  have hlen : (universalRecordBits a).length = 8 + (universalNextOnes a.state + 1) := by
    rw [universal_record_shape]
    simp only [List.length_append, List.length_ofFn, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  have hfixed := universal_skip_fixed base dest rem table state sp 7 0 l.length rfl
  have hunary := universal_skip_unary base dest rem table state sp
    (universalNextOnes a.state) (l ++ List.ofFn (universalActionBits a)) r
    (by simpa [universal_record_shape, List.append_assoc] using ht)
  rw [hlen, MultiTapeTM.runFrom_add]
  have hf : universalInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp) 8 =
      universalEvalCfg base (.skipUnary dest rem) table (l.length + 8) state sp := by
    simpa only [Nat.cast_ofNat, Int.add_assoc, show (7 : ℤ) + 1 = 8 from rfl] using hfixed
  rw [hf]
  simpa only [List.length_append, List.length_ofFn, Nat.cast_add, Nat.cast_ofNat,
    Int.add_assoc] using hunary

/-- A bounded request skips precisely the specified nonempty list of records.

**Proof sketch.** Execute the first record and decrement the record counter.
The last record enters the requested continuation. Run addition adds the
serialized lengths, without an extra transition between consecutive records. -/
private lemma universal_skip_records {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9))
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (as : List (Action 1 Bool (Fin (n + 1)))) (l r : List Bool)
    (rem : Fin 9) (hlen : as.length = rem.val + 1)
    (ht : table = l ++ as.flatMap universalRecordBits ++ r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp)
      (as.flatMap universalRecordBits).length =
    universalEvalCfg base (universalSkipDone dest) table
      (l.length + (as.flatMap universalRecordBits).length) state sp := by
  induction as generalizing l rem with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons a as ih =>
    have hv : rem.val = as.length := by simp only [List.length_cons] at hlen; omega
    have he := universal_skip_record base dest rem table state sp a l
      (as.flatMap universalRecordBits ++ r)
      (by simpa only [List.flatMap_cons, List.append_assoc] using ht)
    rw [List.flatMap_cons, List.length_append, MultiTapeTM.runFrom_add, he]
    cases as with
    | nil => simp [hv]
    | cons b bs =>
      have hn : rem.val ≠ 0 := by simp only [List.length_cons] at hv; omega
      rw [dif_neg hn]
      have htail : (b :: bs).length = rem.val - 1 + 1 := by
        simp only [List.length_cons] at hv ⊢
        omega
      have hi := ih (l ++ universalRecordBits a) ⟨rem.val - 1, by omega⟩ htail
        (by simpa only [List.flatMap_cons, List.append_assoc] using ht)
      convert hi using 1 <;>
        simp only [List.length_append, Nat.cast_add] <;> congr 1 <;> omega

/-- Each erased unary state symbol skips exactly nine transition records.

**Proof sketch.** Erase the first remaining state symbol, run the nine-record
scanner, and repeat for the remaining groups. At the final blank one transition
enters the state rewind. The state-window invariant records all erasures. -/
private lemma universal_skip_groups {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9) (table : List Bool)
    (groups : List (List (Action 1 Bool (Fin (n + 1)))))
    (hg : ∀ g ∈ groups, g.length = 9) (l r : List Bool) (j : ℕ)
    (ht : table = l ++ groups.flatMap (fun g => g.flatMap universalRecordBits) ++ r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length
        (universalStateWindow j groups.length) (j + 1))
      (groups.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length + 1) =
    universalEvalCfg base (.rewindState (some index)) table
      (l.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length)
      (universalStateWindow (j + groups.length) 0) (j + groups.length + 1) := by
  induction groups generalizing l j with
  | nil =>
    simp only [List.length_nil, List.flatMap_nil, Nat.add_zero, Nat.zero_add,
      Nat.cast_zero, add_zero, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base (.group index) (.rewindState (some index))
      table l.length (universalStateWindow j 0) (j + 1) 0 0 none
      (by simp [universalInterpreter, universalFour, universalStateWindow_end])
    simpa using he
  | cons g gs ih =>
    have hgl : g.length = 9 := hg g (by simp)
    have he := universalEval_step base (.group index) (.skipFixed (some index) 8 0)
      table l.length (universalStateWindow j (gs.length + 1)) (j + 1) 0 .pos (some none)
      (by simp [universalInterpreter, universalFour, universalStateWindow_read])
    have hskip := universal_skip_records base (some index) table
      (universalStateWindow (j + 1) gs.length) (j + 2) g l
      (gs.flatMap (fun g => g.flatMap universalRecordBits) ++ r) 8 hgl
      (by simpa [List.flatMap_cons, List.append_assoc] using ht)
    have hrest := ih (fun a ha => hg a (by simp [ha]))
      (l ++ g.flatMap universalRecordBits) (j + 1)
      (by simpa [List.flatMap_cons, List.append_assoc] using ht)
    have htime : (g :: gs).length +
        ((g :: gs).flatMap (fun g => g.flatMap universalRecordBits)).length + 1 =
        1 + (g.flatMap universalRecordBits).length +
          (gs.length + (gs.flatMap (fun g => g.flatMap universalRecordBits)).length + 1) := by
      simp only [List.length_cons, List.flatMap_cons, List.length_append]; omega
    rw [htime, MultiTapeTM.runFrom_add _ (1 + (g.flatMap universalRecordBits).length)
      (gs.length + (gs.flatMap (fun g => g.flatMap universalRecordBits)).length + 1),
      MultiTapeTM.runFrom_add _ 1 (g.flatMap universalRecordBits).length]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero, he]
    simp only [SignType.coe_zero, add_zero, SignType.pos_eq_one, SignType.coe_one,
      universalStateWindow_erase]
    rw [show (j : ℤ) + 1 + 1 = j + 2 by omega, hskip]
    simpa only [universalSkipDone, List.flatMap_cons, List.length_append, List.length_cons,
      Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Int.add_assoc, Int.add_left_comm, Int.add_comm, Int.reduceAdd] using hrest

/-- Reading fixed action fields fills the finite eight-bit register exactly.

**Proof sketch.** The register already agrees with the record before the current
field. Read and update that field, maintaining agreement on a longer prefix.
After field seven the agreement covers every register entry. -/
private lemma universal_read_fixed {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (table : List Bool)
    (state : ℤ → Option Bool) (sp : ℤ) (bits : Fin 8 → Bool) (l r : List Bool)
    (ht : table = l ++ List.ofFn bits ++ r) :
    ∀ (n : ℕ) (field : Fin 8) (old : Fin 8 → Bool), field.val + n = 7 →
      (∀ i : Fin 8, i.val < field.val → old i = bits i) →
      universalInterpreter.runFrom
        (universalEvalCfg base (.readAction field old) table
          (l.length + field.val) state sp) (n + 1) =
      universalEvalCfg base (.nextState bits) table (l.length + 8) state sp := by
  intro n
  induction n with
  | zero =>
    intro field old hf hknown
    have hv : field.val = 7 := by omega
    have hr : bufferTape table (l.length + field.val : ℤ) = some (bits field) := by
      rw [← Nat.cast_add, bufferTape_nat, ht, List.append_assoc,
        List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left (by simpa using field.isLt), List.getElem?_ofFn]
      simp only [field.isLt, ↓reduceDIte]
    have hb : Function.update old field (bits field) = bits := by
      funext i
      by_cases hi : i = field
      · subst i; simp
      · rw [Function.update_of_ne hi]
        apply hknown
        have hn : i.val ≠ field.val := fun h => hi (Fin.ext h)
        omega
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := universalEval_step base (.readAction field old) (.nextState bits)
      table (l.length + field.val) state sp .pos 0 none
      (by
        simp only [universalInterpreter, universalFour, ↓reduceIte, hr]
        simp only [hv, ↓reduceDIte, hb])
    rw [he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    congr 1
    omega
  | succ n ih =>
    intro field old hf hknown
    have hv : field.val ≠ 7 := by omega
    have hr : bufferTape table (l.length + field.val : ℤ) = some (bits field) := by
      rw [← Nat.cast_add, bufferTape_nat, ht, List.append_assoc,
        List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left (by simpa using field.isLt), List.getElem?_ofFn]
      simp only [field.isLt, ↓reduceDIte]
    have hb : ∀ i : Fin 8, i.val < field.val + 1 →
        Function.update old field (bits field) i = bits i := by
      intro i hi
      by_cases he : i = field
      · subst i; simp
      · rw [Function.update_of_ne he]
        apply hknown
        have hn : i.val ≠ field.val := fun h => he (Fin.ext h)
        omega
    have he := universalEval_step base (.readAction field old)
      (.readAction ⟨field.val + 1, by omega⟩ (Function.update old field (bits field)))
      table (l.length + field.val) state sp .pos 0 none
      (by simp [universalInterpreter, universalFour, hr, hv])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert ih ⟨field.val + 1, by omega⟩ _ (by simp; omega) hb using 1 <;>
      simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one] <;> congr 1 <;> omega

/-- Successor decoding, copying, and rewinding cost, before applying the action. -/
private def universalNextCost {n : ℕ} : Option (Fin (n + 1)) → ℕ
  | none => 1
  | some q => 2 * q.val + 4

/-- Decode the successor field and install its unary state at cursor one.

**Proof sketch.** A halting flag takes one transition. A live flag takes one,
copying its index takes `q+1`, and rewinding the new state takes `q+2`.
The table cursor stops on the field's false terminator in both cases. -/
private lemma universal_prepare_next {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (table : List Bool) (bits : Fin 8 → Bool)
    (next : Option (Fin (n + 1))) (l r : List Bool)
    (ht : table = l ++ List.replicate (universalNextOnes next) true ++ false :: r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.nextState bits) table l.length (universalStateTape 0) 1)
      (universalNextCost next) =
    universalEvalCfg base (.applyRecord bits next.isNone) table
      (l.length + universalNextOnes next) (universalStateTape ((next.map Fin.val).getD 0)) 1 := by
  cases next with
  | none =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa [universalNextOnes] using universal_table_read l r false
    have he := universalEval_step base (.nextState bits) (.applyRecord bits true)
      table l.length (universalStateTape 0) 1 0 0 none
      (by simp [universalInterpreter, universalFour, hr])
    simpa [universalNextCost, universalNextOnes, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero] using he
  | some q =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [universalNextOnes, List.replicate_succ, List.append_assoc] using
        universal_table_read l (List.replicate q.val true ++ false :: r) true
    have he := universalEval_step base (.nextState bits) (.copyState bits)
      table l.length (universalStateTape 0) 1 .pos 0 none
      (by simp [universalInterpreter, universalFour, hr])
    have hcopy := universal_unary_copy base (.copyState bits) (.rewindNext bits) 0 table
      (by intro inp work h; simp [universalInterpreter, h])
      (by intro inp work h; simp [universalInterpreter, h]) q.val 0 (l ++ [true]) r
      (by simpa [universalNextOnes, List.replicate_succ, List.append_assoc] using ht)
    have hrew := universal_state_rewind base (.rewindNext bits) (.applyRecord bits false)
      table (l.length + q.val + 1) (universalStateTape q.val)
      (universalStateTape_marker q.val).1 (universalStateTape_marker q.val).2
      (by intro inp work h; simp [universalInterpreter, h])
      (by intro inp work h; simp [universalInterpreter, h]) (q.val + 1)
    have hc : universalInterpreter.runFrom
        (universalEvalCfg base (.copyState bits) table (l.length + 1) (universalStateTape 0) 1)
        (q.val + 1) =
      universalEvalCfg base (.rewindNext bits) table (l.length + q.val + 1)
        (universalStateTape q.val) (q.val + 1) := by
      simpa [List.length_append, Int.add_assoc, Int.add_comm 1] using hcopy
    change universalInterpreter.runFrom _ (2 * q.val + 4) = _
    rw [show 2 * q.val + 4 = 1 + (q.val + 1) + (q.val + 2) by omega,
      MultiTapeTM.runFrom_add _ (1 + (q.val + 1)) (q.val + 2),
      MultiTapeTM.runFrom_add _ 1 (q.val + 1)]
    rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [hc]
    simpa only [universalNextOnes, Option.isNone_some, Option.map_some, Option.getD_some,
      Nat.cast_add, Nat.cast_one, Nat.add_assoc, Int.add_assoc] using hrew

/-- The nine actions for a state, in input-major, work-minor order. -/
private def universalActions (M : CodeTM) (q : Fin (M.numStates + 1)) :
    List (Action 1 Bool (Fin (M.numStates + 1))) :=
  ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
    ([none, some false, some true] : List (Option Bool)).map fun work =>
      M.tm.tr q inp (fun _ => work)

/-- Each state contributes nine records and the read offset selects its action. -/
private lemma universalActions_lookup (M : CodeTM) (q : Fin (M.numStates + 1))
    (inp work : Option Bool) :
    (universalActions M q).length = 9 ∧
    (universalActions M q)[(universalRecordIndex inp work).val]'(by
      change (universalRecordIndex inp work).val < 9
      exact (universalRecordIndex inp work).isLt) = M.tm.tr q inp (fun _ => work) := by
  constructor
  · rfl
  · rcases inp with _ | (_ | _) <;> rcases work with _ | (_ | _) <;> rfl

/-- Count prefix and initial-state field, excluding transition records. -/
private def universalHeader (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates) [] ++ List.replicate M.tm.q₀.val true ++ [false]

/-- Serialization as a header followed by the ordered lists of nine actions. -/
private lemma universal_serialization_actions (M : CodeTM) :
    M.serialize = universalHeader M ++
      ((List.finRange (M.numStates + 1)).map (universalActions M)).flatMap
        (fun g => g.flatMap universalRecordBits) := by
  have hr : M.serialize = pairEncode (Nat.bits M.numStates)
      (List.replicate M.tm.q₀.val true ++ false :: universalRecords M) := by
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
  rw [hr]
  simp [pairEncode, universalHeader, universalRecords, universalActions,
    List.flatMap_map, List.append_assoc]

/-- Decompose the canonical table at the action selected by state and reads.

**Proof sketch.** Split the increasing state enumeration at the source state,
and split its nine-entry list at the read offset. The two prefixes are exactly
the groups and records traversed by the controller. -/
private lemma universal_lookup_parts (M : CodeTM) (q : Fin (M.numStates + 1))
    (inp work : Option Bool) :
    ∃ (groups : List (List (Action 1 Bool (Fin (M.numStates + 1)))))
      (before : List (Action 1 Bool (Fin (M.numStates + 1)))) (after : List Bool),
      groups.length = q.val ∧ (∀ g ∈ groups, g.length = 9) ∧
      before.length = (universalRecordIndex inp work).val ∧
      M.serialize = universalHeader M ++
        groups.flatMap (fun g => g.flatMap universalRecordBits) ++
        before.flatMap universalRecordBits ++
        universalRecordBits (M.tm.tr q inp (fun _ => work)) ++ after := by
  let states := List.finRange (M.numStates + 1)
  let index := universalRecordIndex inp work
  let actions := universalActions M q
  have hq : q.val < states.length := by simpa [states] using q.isLt
  have hi : index.val < actions.length := by
    rw [(universalActions_lookup M q inp work).1]
    exact index.isLt
  have hs : states = states.take q.val ++ q :: states.drop (q.val + 1) := by
    have h := List.take_append_drop q.val states
    rw [List.drop_eq_getElem_cons hq] at h
    simpa [states] using h.symm
  have ha : actions = actions.take index.val ++
      M.tm.tr q inp (fun _ => work) :: actions.drop (index.val + 1) := by
    have h := List.take_append_drop index.val actions
    rw [List.drop_eq_getElem_cons hi, (universalActions_lookup M q inp work).2] at h
    exact h.symm
  refine ⟨(states.take q.val).map (universalActions M), actions.take index.val,
    (actions.drop (index.val + 1)).flatMap universalRecordBits ++
      ((states.drop (q.val + 1)).map (universalActions M)).flatMap
        (fun g => g.flatMap universalRecordBits), ?_, ?_, ?_, ?_⟩
  · simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hq)]
  · intro g hg
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hg
    exact (universalActions_lookup M s none none).1
  · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    rfl
  · rw [universal_serialization_actions]
    change universalHeader M ++ (states.map (universalActions M)).flatMap _ = _
    conv_lhs => rw [hs, List.map_append, List.map_cons, List.flatMap_append,
      List.flatMap_cons]
    change universalHeader M ++ (_ ++ (actions.flatMap universalRecordBits ++ _)) = _
    conv_lhs => rw [ha]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- Decoding the four fixed pairs recovers the source action fields. -/
private lemma universalActionBits_decode {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    universalSign (universalActionBits a 0) (universalActionBits a 1) = a.inputTape ∧
    universalWrite (universalActionBits a 2) (universalActionBits a 3) = (a.workTapes 0).1 ∧
    universalSign (universalActionBits a 4) (universalActionBits a 5) = (a.workTapes 0).2 ∧
    (if universalActionBits a 6 then some (universalActionBits a 7) else none) = a.output := by
  simp only [universalActionBits]
  constructor
  · cases a.inputTape <;> rfl
  constructor
  · rcases (a.workTapes 0).1 with _ | (_ | (_ | _)) <;> rfl
  constructor
  · cases (a.workTapes 0).2 <;> rfl
  · rcases a.output with _ | (_ | _) <;> rfl

/-- Applying the decoded record commutes with the complete source checkpoint.

**Proof sketch.** Decode the four fixed pairs. The virtual-input movement lemma
supplies both the physical head equality and the marker-head equality. Optional
writes and emissions then agree field by field; the newly installed unary state
is precisely the successor representation, including the halting case. -/
private lemma universal_apply_record (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (oldp p : ℕ)
    (a : Action 1 Bool (Fin (M.numStates + 1))) :
    universalInterpreter.step
      (universalEvalCfg (universalSimulationCfg M α src oldp)
        (.applyRecord (universalActionBits a) a.state.isNone) M.serialize p
        (universalStateTape ((a.state.map Fin.val).getD 0)) 1) =
    universalSimulationCfg M α (a.apply src) p := by
  let base := universalSimulationCfg M α src oldp
  let cfg := universalEvalCfg base (.applyRecord (universalActionBits a) a.state.isNone)
    M.serialize p (universalStateTape ((a.state.map Fin.val).getD 0)) 1
  let d := virtualMove (decide (bufferTape [true] (src.inputPos.val : ℤ) ≠ some true))
    src.inputSymbol a.inputTape
  have hi : (if base.workTapeSymbols 3 = some true then none else base.inputSymbol) =
      src.inputSymbol := universalInput_read α src
  have hb := universalActionBits_decode a
  have htr : universalInterpreter.tr
      (.applyRecord (universalActionBits a) a.state.isNone) cfg.inputSymbol cfg.workTapeSymbols =
      (⟨d, universalFour (none, 0) (none, 0) (a.workTapes 0) (none, d), a.output,
        a.state.map (fun _ => .main)⟩ : Action 4 Bool UniversalControl) := by
    have hr3 : cfg.workTapeSymbols 3 = base.workTapeSymbols 3 := rfl
    have hip : cfg.inputSymbol = base.inputSymbol := rfl
    simp only [universalInterpreter, hr3, hip, hi, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
    change (⟨d, universalFour (none, 0) (none, 0) (a.workTapes 0) (none, d), a.output,
      if a.state.isNone then none else some .main⟩ : Action 4 Bool UniversalControl) = _
    cases a.state <;> rfl
  change (universalInterpreter.tr _ cfg.inputSymbol cfg.workTapeSymbols).apply cfg = _
  rw [htr]
  have hmove := universalInput_move α src a.inputTape
  refine Cfg.ext rfl hmove.1 ?_ ?_ rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact add_zero _
    · exact add_zero _
    · rfl
    · exact hmove.2

/-- Select a record by destructive state counting and the bounded read offset.

**Proof sketch.** Skip the preceding state groups while erasing the unary state.
Rewind the erased state tape to one, then skip the read-offset prefix. An offset
of zero enters the action reader directly. The table scans cost their total
serialized length, and state administration costs twice the old index plus three. -/
private lemma universal_select {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9) (table : List Bool)
    (groups : List (List (Action 1 Bool (Fin (n + 1)))))
    (hg : ∀ g ∈ groups, g.length = 9)
    (before : List (Action 1 Bool (Fin (n + 1)))) (hb : before.length = index.val)
    (l r : List Bool)
    (ht : table = l ++ groups.flatMap (fun g => g.flatMap universalRecordBits) ++
      before.flatMap universalRecordBits ++ r) :
    universalInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length
        (universalStateTape groups.length) 1)
      (2 * groups.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length +
        (before.flatMap universalRecordBits).length + 3) =
    universalEvalCfg base (.readAction 0 (fun _ => false)) table
      (l.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length +
        (before.flatMap universalRecordBits).length) (universalStateTape 0) 1 := by
  let pg := groups.flatMap (fun g => g.flatMap universalRecordBits)
  let pb := before.flatMap universalRecordBits
  let next := if h : index.val = 0 then UniversalControl.readAction 0 (fun _ => false)
    else .skipFixed none ⟨index.val - 1, by omega⟩ 0
  have hgroup := universal_skip_groups base index table groups hg l (pb ++ r) 0
    (by simpa [pg, pb, List.append_assoc] using ht)
  have hgr : universalInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length (universalStateTape groups.length) 1)
      (groups.length + pg.length + 1) =
    universalEvalCfg base (.rewindState (some index)) table (l.length + pg.length)
      (universalStateTape 0) (groups.length + 1) := by
    simpa only [Nat.cast_zero, zero_add, universalStateWindow_empty,
      universalStateWindow_zero] using hgroup
  have hrew := universal_state_rewind base (.rewindState (some index)) next table
    (l.length + pg.length) (universalStateTape 0)
    (universalStateTape_marker 0).1 (universalStateTape_marker 0).2
    (by intro inp work h; simp [universalInterpreter, h, next])
    (by intro inp work h; simp [universalInterpreter, h]) (groups.length + 1)
  have hrw : universalInterpreter.runFrom
      (universalEvalCfg base (.rewindState (some index)) table (l.length + pg.length)
        (universalStateTape 0) (groups.length + 1)) (groups.length + 2) =
    universalEvalCfg base next table (l.length + pg.length) (universalStateTape 0) 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hrew
  have hskip : universalInterpreter.runFrom
      (universalEvalCfg base next table (l.length + pg.length) (universalStateTape 0) 1)
      pb.length = universalEvalCfg base (.readAction 0 (fun _ => false)) table
        (l.length + pg.length + pb.length) (universalStateTape 0) 1 := by
    by_cases hi : index.val = 0
    · have hz : before = [] := List.length_eq_zero_iff.mp (hb.trans hi)
      simp [next, hi, pb, hz]
    · have hh := universal_skip_records base none table (universalStateTape 0) 1
        before (l ++ pg) r ⟨index.val - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
        (by simpa [pg, pb, List.append_assoc] using ht)
      simpa only [next, dif_neg hi, universalSkipDone, List.length_append, Nat.cast_add]
        using hh
  change universalInterpreter.runFrom _ (2 * groups.length + pg.length + pb.length + 3) = _
  rw [show 2 * groups.length + pg.length + pb.length + 3 =
      (groups.length + pg.length + 1) + (groups.length + 2) + pb.length by omega,
    MultiTapeTM.runFrom_add _ ((groups.length + pg.length + 1) + (groups.length + 2)) pb.length,
    MultiTapeTM.runFrom_add _ (groups.length + pg.length + 1) (groups.length + 2),
    hgr, hrw, hskip]

/-- Concatenate two configuration equalities without unfolding either run. -/
private lemma universal_run_join {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) {a b c : Cfg k Bool Q x} {s t : ℕ}
    (hs : tm.runFrom a s = b) (ht : tm.runFrom b t = c) :
    tm.runFrom a (s + t) = c := by
  rw [MultiTapeTM.runFrom_add, hs, ht]

/-- One live source transition is realized by the existing finite interpreter.

**Proof sketch.** Read the virtual input and mirrored work symbol, rewind the
table, skip its count and initial-state fields, and select the source record.
Read its eight fixed bits, prepare its successor, and apply it. Concatenate the
exact runs. The old cursor, count prefix, and all skipped records are each
bounded by the serialization length; every source state index is below the
number of states. The resulting bound is `3L + 5N + 20`. -/
lemma universal_live_block (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (p : ℕ)
    (hp : p ≤ M.serialize.length) (hs : src.state ≠ none) :
    ∃ d p', 1 ≤ d ∧ d ≤ 3 * M.serialize.length + 5 * (M.numStates + 1) + 20 ∧
      p' ≤ M.serialize.length ∧
      universalInterpreter.runFrom (universalSimulationCfg M α src p) d =
        universalSimulationCfg M α (M.tm.step src) p' := by
  cases hq : src.state with
  | none => exact False.elim (hs hq)
  | some q =>
    let base := universalSimulationCfg M α src p
    let index := universalRecordIndex src.inputSymbol (src.workTapeSymbols 0)
    let a := M.tm.tr q src.inputSymbol (fun _ => src.workTapeSymbols 0)
    obtain ⟨groups, before, after, hglen, hg, hblen, hparts⟩ :=
      universal_lookup_parts M q src.inputSymbol (src.workTapeSymbols 0)
    let pg := groups.flatMap (fun g => g.flatMap universalRecordBits)
    let pb := before.flatMap universalRecordBits
    let count := pairEncode (Nat.bits M.numStates) []
    let k := 2 * (Nat.bits M.numStates).length + 2
    let pre := universalHeader M ++ pg ++ pb
    let bits := universalActionBits a
    let p' := pre.length + 8 + universalNextOnes a.state
    let selectTime := 2 * q.val + pg.length + pb.length + 3
    let d := 1 + (p + 1) + k + (M.tm.q₀.val + 1) + selectTime + 8 +
      universalNextCost a.state + 1
    have hclen : count.length = k := by
      simpa [count, k] using universal_pair_length (Nat.bits M.numStates) []
    have hhlen : (universalHeader M).length = k + M.tm.q₀.val + 1 := by
      change (count ++ List.replicate M.tm.q₀.val true ++ [false]).length = _
      simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil, hclen]
    have hplen : pre.length = (universalHeader M).length + pg.length + pb.length := by
      simp only [pre, List.length_append]
    have ht : M.serialize = pre ++ universalRecordBits a ++ after := by
      simpa only [pre, pg, pb, a, List.append_assoc] using hparts
    have hcfg : base = universalEvalCfg base .main M.serialize p (universalStateTape q.val) 1 := by
      simp only [base, universalSimulationCfg, universalEvalCfg, hq,
        Option.map_some, Option.getD_some]
      rfl
    have hi : (if base.workTapeSymbols 3 = some true then none else base.inputSymbol) =
        src.inputSymbol := universalInput_read α src
    have hmain : universalInterpreter.runFrom base 1 =
        universalEvalCfg base (.rewindTable false index) M.serialize (p - 1)
          (universalStateTape q.val) 1 := by
      rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero]
      conv_lhs => rw [hcfg]
      have he := universalEval_step base .main (.rewindTable false index)
        M.serialize p (universalStateTape q.val) 1 .neg 0 none (by
          change universalAdmin (.rewindTable false (universalRecordIndex
            (if base.workTapeSymbols 3 = some true then none else base.inputSymbol)
            (base.workTapeSymbols 2))) .neg = _
          rw [hi]
          rfl)
      simpa only [SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.coe_zero,
        add_zero, sub_eq_add_neg] using he
    have hrew := universal_table_rewind base false index M.serialize
      (universalStateTape q.val) 1 p hp
    have hcount := universal_count_run base false index M.serialize
      (universalStateTape q.val) 1 (Nat.bits M.numStates) []
      (List.replicate M.tm.q₀.val true ++ false :: (pg ++ pb ++ universalRecordBits a ++ after))
      (by simpa [universalHeader, pairEncode, pg, pb, a, List.append_assoc] using hparts)
    have hc : universalInterpreter.runFrom
        (universalEvalCfg base (.countFirst false index) M.serialize 0 (universalStateTape q.val) 1) k =
      universalEvalCfg base (.initialSkip index) M.serialize k (universalStateTape q.val) 1 := by
      simpa only [Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.cast_zero,
        zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hcount
    have hinit := universal_initial_skip base index M.serialize (universalStateTape q.val) 1
      M.tm.q₀.val count (pg ++ pb ++ universalRecordBits a ++ after)
      (by simpa [count, universalHeader, pg, pb, a, List.append_assoc] using hparts)
    have hinit' : universalInterpreter.runFrom
        (universalEvalCfg base (.initialSkip index) M.serialize k (universalStateTape q.val) 1)
        (M.tm.q₀.val + 1) =
      universalEvalCfg base (.group index) M.serialize (universalHeader M).length
        (universalStateTape q.val) 1 := by
      simpa only [hclen, hhlen, Nat.cast_add, Nat.cast_one] using hinit
    have hselect := universal_select base index M.serialize groups hg before hblen
      (universalHeader M) (universalRecordBits a ++ after)
      (by simpa only [a, List.append_assoc] using hparts)
    have hsel : universalInterpreter.runFrom
        (universalEvalCfg base (.group index) M.serialize (universalHeader M).length
          (universalStateTape q.val) 1) selectTime =
      universalEvalCfg base (.readAction 0 (fun _ => false)) M.serialize pre.length
        (universalStateTape 0) 1 := by
      simpa only [hglen, hplen, Nat.cast_add] using hselect
    have hread := universal_read_fixed base M.serialize (universalStateTape 0) 1 bits pre
      (List.replicate (universalNextOnes a.state) true ++ false :: after)
      (by simpa [universal_record_shape, bits, List.append_assoc] using ht)
      7 0 (fun _ => false) rfl (by intro i hi; exact False.elim (Nat.not_lt_zero _ hi))
    have hrd : universalInterpreter.runFrom
        (universalEvalCfg base (.readAction 0 (fun _ => false)) M.serialize pre.length
          (universalStateTape 0) 1) 8 =
      universalEvalCfg base (.nextState bits) M.serialize (pre.length + 8)
        (universalStateTape 0) 1 := by
      simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using hread
    have hnext := universal_prepare_next base M.serialize bits a.state
      (pre ++ List.ofFn bits) after
      (by simpa [universal_record_shape, bits, List.append_assoc] using ht)
    have hn : universalInterpreter.runFrom
        (universalEvalCfg base (.nextState bits) M.serialize (pre.length + 8)
          (universalStateTape 0) 1) (universalNextCost a.state) =
      universalEvalCfg base (.applyRecord bits a.state.isNone) M.serialize p'
        (universalStateTape ((a.state.map Fin.val).getD 0)) 1 := by
      simpa only [p', List.length_append, List.length_ofFn, Nat.cast_add, Nat.cast_ofNat] using hnext
    have happly : universalInterpreter.runFrom
        (universalEvalCfg base (.applyRecord bits a.state.isNone) M.serialize p'
          (universalStateTape ((a.state.map Fin.val).getD 0)) 1) 1 =
      universalSimulationCfg M α (a.apply src) p' := by
      rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero]
      exact universal_apply_record M α src p p' a
    have hrun := universal_run_join universalInterpreter
      (universal_run_join universalInterpreter
        (universal_run_join universalInterpreter
          (universal_run_join universalInterpreter
            (universal_run_join universalInterpreter
              (universal_run_join universalInterpreter
                (universal_run_join universalInterpreter hmain hrew) hc) hinit') hsel) hrd) hn) happly
    have hstep : M.tm.step src = a.apply src := by
      have hw : src.workTapeSymbols = fun _ : Fin 1 => src.workTapeSymbols 0 := by
        funext i
        rw [Fin.eq_zero i]
      simp only [MultiTapeTM.step, hq]
      rw [hw]
    have hlength : M.serialize.length = pre.length + 8 +
        universalNextOnes a.state + 1 + after.length := by
      rw [ht, universal_record_shape]
      simp only [List.length_append, List.length_ofFn, List.length_replicate,
        List.length_cons, List.length_nil]
      omega
    have hnextBound : universalNextCost a.state ≤ 2 * (M.numStates + 1) + 4 := by
      cases hnxt : a.state with
      | none => simp [universalNextCost]
      | some q' => have hq' := q'.isLt; simp only [universalNextCost]; omega
    have hqb := q.isLt
    have hq₀b := M.tm.q₀.isLt
    refine ⟨d, p', ?_, ?_, ?_, ?_⟩
    · dsimp only [d]; omega
    · dsimp only [d, selectTime]
      rw [hplen, hhlen] at hlength
      omega
    · dsimp only [p']; omega
    · rw [hstep]
      exact hrun

/-- Code-dependent block budget for the concrete interpreter. The intended
ledger is recorded in the delivery report; its realization is the remaining
concrete-step obligation in `universal`.

**Completion (epoch 3B2).** `universal_live_block` realizes that ledger and proves
this unchanged budget. Halting blocks cost `h+k+q₀+2q+P+16`; live successors
cost `h+k+q₀+2q+P+2q′+19`, with the symbols defined in the delivery report. -/
def universalBlockBound (c : EffectiveMachineCode) (α : List Bool) : ℕ :=
  3 * (c.decode α).serialize.length + 5 * ((c.decode α).numStates + 1) + 20

/-- Concrete checkpoint relation. The bound on the table cursor is needed for
a uniform rewind cost; inactive canonizer tapes remain existentially framed. -/
def universalRelation (c : EffectiveMachineCode) (α x : List Bool)
    (src : Cfg 1 Bool (Fin ((c.decode α).numStates + 1)) x)
    (dst : Cfg (universalTM c).k Bool (universalTM c).State (pairEncode α x)) : Prop :=
  ∃ (p : ℕ) (tapes : Fin (universalCanonTM c).k → ℤ → Option Bool)
    (heads : Fin (universalCanonTM c).k → ℤ), p ≤ (c.decode α).serialize.length ∧
    dst = rightCfg Sum.inr (universalSimulationCfg (c.decode α) α src p) tapes heads

/-- The canonical header ends inside its table buffer. -/
private lemma universal_header_bound (M : CodeTM) :
    2 * (Nat.bits M.numStates).length + 2 + M.tm.q₀.val + 1 ≤ M.serialize.length := by
  obtain ⟨records, hr⟩ := universal_serialization_header M
  rw [hr, universal_pair_length]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- Full startup supplies the concrete checkpoint relation. -/
lemma universalRelation_start (c : EffectiveMachineCode) (α x : List Bool) :
    ∃ t, t ≤ universalStartupBound c α ∧
      universalRelation c α x ((c.decode α).tm.initCfg x)
        ((universalTM c).tm.runFrom ((universalTM c).tm.initCfg (pairEncode α x)) t) := by
  obtain ⟨t, tapes, heads, ht, he⟩ := universal_initialized c α x
  exact ⟨t, ht, _, tapes, heads, universal_header_bound _, he⟩

/-- The concrete checkpoint relation preserves halting in both directions. -/
lemma universalRelation_halt (c : EffectiveMachineCode) (α x : List Bool)
    (src : Cfg 1 Bool (Fin ((c.decode α).numStates + 1)) x)
    (dst : Cfg (universalTM c).k Bool (universalTM c).State (pairEncode α x))
    (h : universalRelation c α x src dst) : src.state = none ↔ dst.state = none := by
  obtain ⟨p, tapes, heads, -, rfl⟩ := h
  simp only [rightCfg, universalSimulationCfg, Option.map_eq_none_iff]

/-- The concrete checkpoint relation preserves the complete accumulated output. -/
lemma universalRelation_output (c : EffectiveMachineCode) (α x : List Bool)
    (src : Cfg 1 Bool (Fin ((c.decode α).numStates + 1)) x)
    (dst : Cfg (universalTM c).k Bool (universalTM c).State (pairEncode α x))
    (h : universalRelation c α x src dst) : src.output = dst.output := by
  obtain ⟨p, tapes, heads, -, rfl⟩ := h
  rfl

end Turing
