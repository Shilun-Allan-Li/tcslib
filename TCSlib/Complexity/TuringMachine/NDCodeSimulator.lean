/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.CodeSimulator
import TCSlib.Complexity.TuringMachine.ChoiceReplay
import TCSlib.Complexity.TuringMachine.Build.InputWindow
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.TuringMachine.Build.SeamLayout
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.TuringMachine.Build.InputRewind
import TCSlib.Complexity.TuringMachine.Build.InterpreterStartup

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The interpreter core for nondeterministic codes

The code layer and the interpreter core that the universal NDTM and the diagonalizer of
`TCSlib.Complexity.Diagonalization.NTimeHierarchy` share ([AB09, Exercise 2.6]: a universal
NDTM; at linear overhead, decision CH34-Q8). Nondeterministic codes are interpreted through
their **replay machine** (user decision 3 of 2026-10-13): per code, the deterministic
three-work-tape serialization of the decoded machine's replay machine is computed, and the
deterministic step block (host H2) runs it at `k = 3`, unchanged, with the choice word on the
mirrored choice tape. No nondeterministic `Turing.MachineFormat`, no third parse layer, and no
change to `TCSlib.Complexity.TuringMachine.NDCodes`.

## Design

* **The bridge** `Turing.CodeNDTM.serialize_eq_tableBitsK` (proved) states the fixed ND
  serialization as its own header (the binary state count, the unary initial state) followed by
  the `false`-slice and `true`-slice tables in the generic `Turing.tableBitsK` layout. It is an
  identity of `Turing.CodeNDTM.serialize`, not of the serialization of any deterministic machine:
  no deterministic `k`-record serialization has two tables after one header.
* **The replay canonizer** `Turing.exists_replayCanonizer` keeps that header (the replay machine
  has the same states and initial state) and re-serializes the two tables into the replay
  machine's one table, at `3^4 = 81` records per state rather than `2·27 = 54`.
* **The interpreter core** `Turing.exists_ndInterpreterCore` is deterministic: the stream of
  choices is on a tape before it starts (guess first, user decision 1). Its prefix clause (time in
  the simulated branch's halting time) is kept with no consumer (user, 2026-10-17): the universal
  and the diagonalizer's mid-rung, at a guessed budget, use the total-time clause `C·(t + 1)`.

## Main definitions

No new public definitions: the replay canonizer and the interpreter core are existential
contracts.

## Main results

* `Turing.CodeNDTM.serialize_eq_tableBitsK` — the bridge (proved).
* `Turing.exists_replayCanonizer` — the per-code replay canonizer (proved).
* `Turing.exists_ndInterpreterCore` — the interpreter core `R` (proved).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, §1.4.1: machine codes and the universal machine;
  §2.1.2; Exercise 2.6: the universal NDTM.)
-/

namespace Turing

/-- **The ND serialization as two deterministic tables.** The fixed serialization of a coded
NDTM is the binary state count paired with the unary initial state followed by the `false`-slice
table and then the `true`-slice table, each in the generic `k`-record layout `Turing.tableBitsK`
at `k = 2`. This identity concerns `Turing.CodeNDTM.serialize` with its own header; it is not an
identity with `Turing.serializeK` of any deterministic machine. [AB09, §1.4]

**Proof sketch.** At two work tapes the generic table writer is `Turing.codeTable2Bits`
(`Turing.tableBitsK_two`); unfold the serialization over the choice bit. -/
theorem CodeNDTM.serialize_eq_tableBitsK (M : CodeNDTM) :
    M.serialize = pairEncode (Nat.bits M.numStates)
      (unaryFin M.tm.q₀ ++ (tableBitsK (M.tm.fixChoice false).tr ++
        tableBitsK (M.tm.fixChoice true).tr)) := by
  rw [tableBitsK_two, tableBitsK_two]
  simp [CodeNDTM.serialize, codeTable2Bits, NDTM.fixChoice, actionBits₂_eq_actionBitsK]

/-! ### The replay canonizer's list function -/

/-- A two-work-tape record widened to three work tapes: the choice tape's field `(none, +1)`
(the bits `false, false, true, false`) inserted after the input move and the two work-tape
fields, which take the record's first ten bits. -/
private def rc_widen (r : List Bool) : List Bool :=
  r.take 10 ++ [false, false, true, false] ++ r.drop 10

/-- One round of the re-emission: peel one record off each slice table and emit the widened
`false` record twice and the widened `true` record (the choice reads blank, `false`, `true`). -/
private def rc_round (n : ℕ) (p : List Bool × List Bool × List Bool) :
    List Bool × List Bool × List Bool :=
  match codeSkipActionK 2 n p.2.1, codeSkipActionK 2 n p.2.2 with
  | some f, some t =>
    let rf := p.2.1.take (p.2.1.length - f.length)
    let rt := p.2.2.take (p.2.2.length - t.length)
    (p.1 ++ (rc_widen rf ++ rc_widen rf ++ rc_widen rt), f, t)
  | _, _ => p

/-- The re-emitted table: the `true` table starts after `27 (n + 1)` records of the `false`
table; then `27 (n + 1)` rounds read the two in lockstep. -/
private def rc_table (n : ℕ) (body : List Bool) : List Bool :=
  match codeSkipRepeat (codeSkipActionK 2 n) (27 * (n + 1)) body with
  | none => []
  | some tT => ((rc_round n)^[27 * (n + 1)] ([], body, tT)).1

/-- The replay canonizer's list function: keep the header (the binary state count and the unary
initial state) and re-emit the body by `rc_table`. -/
private def rc_g (xs : List Bool) : List Bool :=
  match pairDecode xs with
  | none => []
  | some (u, v) =>
    match codeReadUnary v with
    | none => []
    | some (_, body) => xs.take (xs.length - body.length) ++ rc_table (codeBitsNat u) body

/-- Skipping `|E|` records of a list of records leaves the rest. -/
private theorem rc_skip {κ : Type} {n : ℕ} (f : κ → Action 2 Bool (Fin (n + 1))) (E : List κ)
    (rest : List Bool) :
    codeSkipRepeat (codeSkipActionK 2 n) E.length (E.flatMap (fun e => actionBitsK (f e)) ++ rest)
      = some rest := by
  induction E with
  | nil => rw [List.length_nil, codeSkipRepeat_zero, List.flatMap_nil, List.nil_append]
  | cons e E ih =>
    rw [List.length_cons, codeSkipRepeat_succ, List.flatMap_cons, List.append_assoc,
      codeSkipActionK_append, Option.bind_some, ih]

/-- One round on two lists that start with records. -/
private theorem rc_round_step {n : ℕ} (a b : Action 2 Bool (Fin (n + 1))) (acc rF rT : List Bool) :
    rc_round n (acc, actionBitsK a ++ rF, actionBitsK b ++ rT) =
      (acc ++ (rc_widen (actionBitsK a) ++ rc_widen (actionBitsK a) ++
        rc_widen (actionBitsK b)), rF, rT) := by
  unfold rc_round
  rw [codeSkipActionK_append, codeSkipActionK_append]
  simp only [List.length_append, Nat.add_sub_cancel, List.take_left]

/-- `|E|` rounds on two lists of records emit the widened triples, record by record. -/
private theorem rc_rounds {κ : Type} {n : ℕ} (fF fT : κ → Action 2 Bool (Fin (n + 1)))
    (E : List κ) (acc restF restT : List Bool) :
    (rc_round n)^[E.length] (acc, E.flatMap (fun e => actionBitsK (fF e)) ++ restF,
        E.flatMap (fun e => actionBitsK (fT e)) ++ restT) =
      (acc ++ E.flatMap (fun e => rc_widen (actionBitsK (fF e)) ++
        rc_widen (actionBitsK (fF e)) ++ rc_widen (actionBitsK (fT e))), restF, restT) := by
  induction E generalizing acc with
  | nil =>
    rw [List.length_nil, Function.iterate_zero_apply, List.flatMap_nil, List.flatMap_nil,
      List.flatMap_nil, List.nil_append, List.nil_append, List.append_nil]
  | cons e E ih =>
    rw [List.length_cons, Function.iterate_succ_apply, List.flatMap_cons, List.flatMap_cons,
      List.append_assoc, List.append_assoc, rc_round_step, ih, List.flatMap_cons,
      List.append_assoc]

/-- The choice tape's field `(none, +1)` in bits. -/
private theorem rc_choiceField :
    optOptBoolBits (none : Option (Option Bool)) ++ signBits (1 : SignType) =
      [false, false, true, false] := by
  rw [optOptBoolBits_none, ← SignType.pos_eq_one, signBits_pos]
  rfl

/-- A move is two bits. -/
private theorem rc_signBits_length (s : SignType) : (signBits s).length = 2 := by
  cases s
  · rw [signBits_zero]; rfl
  · rw [signBits_neg]; rfl
  · rw [signBits_pos]; rfl

/-- A write field is two bits. -/
private theorem rc_optOptBoolBits_length (o : Option (Option Bool)) :
    (optOptBoolBits o).length = 2 := by
  rcases o with _ | (_ | b)
  · rw [optOptBoolBits_none]; rfl
  · rw [optOptBoolBits_some_none]; rfl
  · cases b
    · rw [optOptBoolBits_some_false]; rfl
    · rw [optOptBoolBits_some_true]; rfl

/-- Widening a two-tape record's bits gives the bits of the record with the choice tape's field
`(none, +1)` as its third work tape: decoding and re-emitting the record is not needed. -/
private theorem rc_widen_record {n : ℕ} (a : Action 2 Bool (Fin (n + 1))) :
    actionBitsK (⟨a.inputTape, Fin.lastCases (none, 1) a.workTapes, a.output, a.state⟩ :
        Action 3 Bool (Fin (n + 1))) = rc_widen (actionBitsK a) := by
  have head : (signBits a.inputTape ++ (List.finRange 2).flatMap fun i =>
      optOptBoolBits (a.workTapes i).1 ++ signBits (a.workTapes i).2).length = 10 := by
    simp only [List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
      List.flatMap_cons, List.flatMap_nil, List.length_append, rc_signBits_length,
      rc_optOptBoolBits_length, List.length_nil]
  unfold rc_widen
  rw [actionBitsK_eq, actionBitsK_eq, List.finRange_succ_last, List.flatMap_append,
    List.flatMap_map]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  rw [List.append_assoc (signBits a.inputTape ++ _), List.append_assoc (signBits a.inputTape ++ _),
    List.take_left' head, List.drop_left' head, ← rc_choiceField]
  simp only [List.append_assoc]

/-- At one tape, `Fin.cons a Fin.elim0` is `Fin.snoc Fin.elim0 a`. -/
private theorem rc_cons_elim0 (a : Option Bool) :
    (Fin.cons a Fin.elim0 : Fin 1 → Option Bool) =
      Fin.snoc (Fin.elim0 : Fin 0 → Option Bool) a := by
  funext i
  rw [Fin.fin_one_eq_zero i]
  exact (Fin.snoc_last (α := fun _ => Option Bool) a Fin.elim0).symm

/-- The work reads at `k + 1` tapes, with the new tape's read innermost. -/
private theorem rc_workReads_snoc (k : ℕ) : workReadsK (k + 1) =
    (workReadsK k).flatMap fun w =>
      ([none, some false, some true] : List (Option Bool)).map (Fin.snoc w) := by
  induction k with
  | zero =>
    rw [workReadsK_succ, workReadsK_zero]
    simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
      List.append_nil, List.cons_append, List.nil_append, rc_cons_elim0]
  | succ k ih =>
    have lhs := workReadsK_succ (k + 1)
    rw [ih] at lhs
    rw [lhs, workReadsK_succ k]
    simp only [List.map_flatMap, List.map_map, List.flatMap_assoc, List.flatMap_map,
      Function.comp_def, Fin.cons_snoc_eq_snoc_cons]

/-- The replay machine's record at a choice read is the widened record of the slice the read
selects (a blank selects `false`). -/
private theorem rc_replay_record {n : ℕ} (N : NDTM 2 Bool (Fin (n + 1))) (q : Fin (n + 1))
    (inp : Option Bool) (w : Fin 2 → Option Bool) (wc : Option Bool) :
    actionBitsK (N.replayTM.tr q inp (Fin.snoc w wc)) =
      rc_widen (actionBitsK (N.tr (wc.getD false) q inp w)) := by
  rw [NDTM.replayTM_tr]
  have hw : (fun i : Fin 2 => (Fin.snoc w wc : Fin 3 → Option Bool) i.castSucc) = w := by
    funext i
    exact Fin.snoc_castSucc (α := fun _ => Option Bool) wc w i
  simp only [Fin.snoc_last, hw]
  exact rc_widen_record _

/-- The replay machine's table: for each state, input read and two-tape read, the widened
`false` record twice and then the widened `true` record. -/
private theorem rc_replay_table {n : ℕ} (N : NDTM 2 Bool (Fin (n + 1))) :
    tableBitsK N.replayTM.tr = (List.finRange (n + 1)).flatMap fun q =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
        (workReadsK 2).flatMap fun w =>
          rc_widen (actionBitsK (N.tr false q inp w)) ++
            rc_widen (actionBitsK (N.tr false q inp w)) ++
            rc_widen (actionBitsK (N.tr true q inp w)) := by
  rw [tableBitsK_eq, rc_workReads_snoc 2]
  simp only [List.flatMap_assoc, List.flatMap_map, rc_replay_record, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, Option.getD_none, Option.getD_some, List.append_assoc]

/-- Two work tapes have nine reads (`Turing.StepBlock.length_workReadsK` at `k = 2`). -/
private theorem rc_workReads2_length : (workReadsK 2).length = 9 := by
  rw [StepBlock.length_workReadsK]
  rfl

/-- A table indexed by state, input read and two-tape read is one `flatMap` over the key list. -/
private theorem rc_flat {n : ℕ} {β : Type}
    (h : Fin (n + 1) → Option Bool → (Fin 2 → Option Bool) → List β) :
    ((List.finRange (n + 1)).flatMap fun q =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
        (workReadsK 2).flatMap fun w => h q inp w) =
    ((List.finRange (n + 1)).flatMap fun q =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
        (workReadsK 2).map fun w => (q, inp, w)).flatMap (fun e => h e.1 e.2.1 e.2.2) := by
  simp only [List.flatMap_assoc, List.flatMap_map]

/-- The key list has `27 (n + 1)` entries. -/
private theorem rc_keys_length (n : ℕ) :
    ((List.finRange (n + 1)).flatMap fun q =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
        (workReadsK 2).map fun w => (q, inp, w)).length = 27 * (n + 1) := by
  simp only [List.length_flatMap, List.flatMap_cons, List.flatMap_nil, List.length_append,
    List.length_map, rc_workReads2_length, List.length_nil, List.map_const', List.length_finRange,
    List.sum_replicate_nat]
  omega

/-- `rc_table` maps the two slice tables, concatenated, to the replay machine's table.

**Proof sketch.** Both slice tables and the replay table are one `flatMap` over the same key list
of `27 (n + 1)` entries (`rc_flat`, `rc_keys_length`; the replay table by `rc_replay_table`). The
skip of `27 (n + 1)` records of the `false` table finds the `true` table (`rc_skip`), and as many
rounds emit the widened triples key by key (`rc_rounds`). -/
private theorem rc_table_eq {n : ℕ} (N : NDTM 2 Bool (Fin (n + 1))) :
    rc_table n (tableBitsK (N.fixChoice false).tr ++ tableBitsK (N.fixChoice true).tr) =
      tableBitsK N.replayTM.tr := by
  have hsrc (b : Bool) : tableBitsK (N.fixChoice b).tr = (List.finRange (n + 1)).flatMap fun q =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
        (workReadsK 2).flatMap fun w => actionBitsK (N.tr b q inp w) := by
    rw [tableBitsK_eq]
    simp only [NDTM.fixChoice_tr]
  have hrep : tableBitsK N.replayTM.tr = (List.finRange (n + 1)).flatMap fun q =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
        (workReadsK 2).flatMap fun w =>
          rc_widen (actionBitsK (N.tr false q inp w)) ++
            rc_widen (actionBitsK (N.tr false q inp w)) ++
            rc_widen (actionBitsK (N.tr true q inp w)) := by
    exact rc_replay_table N
  rw [hsrc, hsrc, hrep, rc_flat, rc_flat, rc_flat]
  generalize hE : ((List.finRange (n + 1)).flatMap fun q =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
        (workReadsK 2).map fun w => (q, inp, w)) = E
  have hlen : E.length = 27 * (n + 1) := hE ▸ rc_keys_length n
  unfold rc_table
  rw [← hlen, rc_skip]
  simp only
  have h0 := rc_rounds (fun e => N.tr false e.1 e.2.1 e.2.2)
    (fun e => N.tr true e.1 e.2.1 e.2.2) E
    [] (E.flatMap fun e => actionBitsK (N.tr true e.1 e.2.1 e.2.2)) []
  rw [List.append_nil, List.nil_append] at h0
  rw [h0]

/-- `rc_g` maps the fixed ND serialization of a code to the serialization of its replay machine:
the header is kept, and the body is `rc_table_eq`'s. -/
private theorem rc_g_serialize (M : CodeNDTM) : rc_g M.serialize = serializeK M.tm.replayTM := by
  rw [CodeNDTM.serialize_eq_tableBitsK, serializeK_eq, NDTM.replayTM_q₀, ← rc_table_eq]
  generalize tableBitsK (M.tm.fixChoice false).tr ++ tableBitsK (M.tm.fixChoice true).tr = body
  unfold rc_g
  rw [pairDecode_pairEncode]
  simp only
  rw [unaryFin_eq, List.append_assoc, List.singleton_append, codeReadUnary_append]
  simp only
  rw [codeBitsNat_bits, pairEncode_eq, pairEncode_eq]
  have hsplit : (M.numStates.bits.flatMap fun b => [b, b]) ++ [false, true] ++
      (List.replicate (↑M.tm.q₀) true ++ false :: body) =
      ((M.numStates.bits.flatMap fun b => [b, b]) ++ [false, true] ++
        (List.replicate (↑M.tm.q₀) true ++ [false])) ++ body := by
    simp only [List.append_assoc, List.singleton_append]
  rw [hsplit, List.length_append, Nat.add_sub_cancel, List.take_left]
  simp only [List.append_assoc, List.singleton_append]

/-- The widening is primitive recursive (a prefix, a constant and a suffix). -/
private theorem rc_widen_primrec : Primrec rc_widen := by
  have ht : Primrec fun r : List Bool => r.take (r.length - (r.length - 10)) :=
    codePrimPrefix.comp Primrec.id (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 10))
  have h := Primrec.list_append.comp (Primrec.list_append.comp ht
    (Primrec.const [false, false, true, false])) (codePrimDrop.comp Primrec.id (Primrec.const 10))
  refine h.of_eq fun r => ?_
  unfold rc_widen
  congr 2
  by_cases hr : 10 ≤ r.length
  · rw [Nat.sub_sub_self hr]
  · have h0 : r.length - 10 = 0 := by omega
    rw [h0, Nat.sub_zero, List.take_length, List.take_of_length_le (by omega)]

/-- The rounds' state: the emitted prefix and the two remaining tables. -/
private abbrev rc_State := List Bool × List Bool × List Bool

/-- The round's body once both skips succeed, on `((n, p), f)` and `t`. -/
private def rc_body (q : ((ℕ × rc_State) × List Bool) × List Bool) : rc_State :=
  (q.1.1.2.1 ++ (rc_widen (q.1.1.2.2.1.take (q.1.1.2.2.1.length - q.1.2.length)) ++
    rc_widen (q.1.1.2.2.1.take (q.1.1.2.2.1.length - q.1.2.length)) ++
    rc_widen (q.1.1.2.2.2.take (q.1.1.2.2.2.length - q.2.length))), q.1.2, q.2)

/-- The round's body is primitive recursive. -/
private theorem rc_body_primrec : Primrec rc_body := by
  have hrf : Primrec fun q : ((ℕ × rc_State) × List Bool) × List Bool =>
      rc_widen (q.1.1.2.2.1.take (q.1.1.2.2.1.length - q.1.2.length)) :=
    rc_widen_primrec.comp (codePrimPrefix.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)))
  have hrt : Primrec fun q : ((ℕ × rc_State) × List Bool) × List Bool =>
      rc_widen (q.1.1.2.2.2.take (q.1.1.2.2.2.length - q.2.length)) :=
    rc_widen_primrec.comp (codePrimPrefix.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.list_length.comp Primrec.snd))
  exact Primrec.pair (Primrec.list_append.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.list_append.comp (Primrec.list_append.comp hrf hrf) hrt))
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)

/-- One round is primitive recursive (two record skips, then the body). -/
private theorem rc_round_primrec : Primrec₂ rc_round := by
  have hin := Primrec.option_casesOn (α := (ℕ × rc_State) × List Bool) (σ := rc_State)
      ((codePrimSkipActionK 2).comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.snd.comp Primrec.fst) rc_body_primrec.to₂
  have hout := Primrec.option_casesOn (α := ℕ × rc_State) (σ := rc_State)
      ((codePrimSkipActionK 2).comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      Primrec.snd hin.to₂
  refine hout.of_eq ?_
  rintro ⟨n, acc, F, T⟩
  unfold rc_round
  dsimp only
  rcases codeSkipActionK 2 n F with _ | f <;> rcases codeSkipActionK 2 n T with _ | t <;> rfl

/-- The re-emitted table is primitive recursive (a bounded skip, then a counted iteration). -/
private theorem rc_table_primrec : Primrec₂ rc_table := by
  have hcount : Primrec fun n : ℕ => 27 * (n + 1) :=
    Primrec.nat_mul.comp (Primrec.const 27) Primrec.succ
  have hskip := (codePrimRepeat (fun n => codeSkipActionK 2 n) (codePrimSkipActionK 2)
    (fun n => 27 * (n + 1)) hcount).comp (Primrec.fst (α := ℕ) (β := List Bool)) Primrec.snd
  have hiter : Primrec fun q : (ℕ × List Bool) × List Bool =>
      (rc_round q.1.1)^[27 * (q.1.1 + 1)] (([] : List Bool), q.1.2, q.2) :=
    Primrec.nat_iterate (hcount.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair (Primrec.const []) (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
      (rc_round_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  have h := Primrec.option_casesOn hskip (Primrec.const ([] : List Bool))
    (Primrec.fst.comp hiter).to₂
  refine h.of_eq ?_
  rintro ⟨n, body⟩
  unfold rc_table
  dsimp only
  rcases codeSkipRepeat (codeSkipActionK 2 n) (27 * (n + 1)) body with _ | tT <;> rfl

/-- The replay canonizer's list function is primitive recursive. -/
private theorem rc_g_primrec : Primrec rc_g := by
  have hin := Primrec.option_casesOn (α := List Bool × (List Bool × List Bool)) (σ := List Bool)
      (codePrimUnary.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const []) (Primrec.list_append.comp
        (codePrimPrefix.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)))
        (rc_table_primrec.comp (codePrimBitsNat.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) (Primrec.snd.comp Primrec.snd))).to₂
  have h := Primrec.option_casesOn codePrimPair (Primrec.const ([] : List Bool)) hin.to₂
  refine h.of_eq ?_
  intro xs
  unfold rc_g
  rcases pairDecode xs with _ | ⟨u, v⟩
  · rfl
  · dsimp only
    rcases codeReadUnary v with _ | ⟨m, body⟩ <;> rfl

/-- **The per-code replay canonizer.** For every effective nondeterministic scheme `c` there is
a finite binary machine computing, from a code `α`, the fixed three-work-tape serialization
`Turing.serializeK` of the decoded machine's replay machine `Turing.NDTM.replayTM` (choice tape
last), within some time bound `T` of `|α|` alone. The bound is arbitrary: each code's universal
constant absorbs it. [AB09, §1.4: a code is mapped to its canonical description]

**Proof sketch.** The scheme's canonizer computes `α ↦ (c.decode α).serialize`
(`Turing.EffectiveNDMachineCode.canonizer_computes`). A primitive recursive list function `g`
maps it to `serializeK (c.decode α).tm.replayTM`: it copies the header, splits the two tables
into records by `Turing.codeSkipActionK`, and re-emits them in the order of
`Turing.workReadsK 3`, the choice read innermost (the blank and `false` reads both select the
`false` record). Each record is decoded and re-emitted in the three-tape field order of
`Turing.actionBitsK`: the input move, the first two work-tape fields, then the choice tape's
field `(none, +1)` as the third, then the output and the successor. Compile `g` by
`Turing.codePrim_machine` and compose (`Turing.FinTM.computesFunInTime_comp`; the canonizer's
output length is at most its time).

**Implementation.** The list function is the private `rc_g`. It widens each record at the bit
level, inserting the choice tape's field after the first two work-tape fields (`rc_widen`), which
equals decoding and re-emitting it (`rc_widen_record`); the two tables are read in lockstep, one
record of each per round, for `27 (n + 1)` rounds (`rc_table_eq`). The compiled machine's time
bound is made monotone by a running maximum before the composition. -/
theorem exists_replayCanonizer (c : EffectiveNDMachineCode) :
    ∃ (M : FinTM Bool) (T : ℕ → ℕ),
      M.ComputesFunInTime (fun α => serializeK (c.decode α).tm.replayTM) T := by
  obtain ⟨G, TG, hG⟩ := codePrim_machine rc_g rc_g_primrec
  have hmono : Monotone fun n => (Finset.range (n + 1)).sup TG := fun a b hab =>
    Finset.sup_mono (Finset.range_subset_range.mpr (by omega))
  have hG' : G.ComputesFunInTime rc_g fun n => (Finset.range (n + 1)).sup TG := by
    rw [FinTM.computesFunInTime_iff] at hG ⊢
    intro x
    exact (hG x).mono (Finset.le_sup (Finset.mem_range.mpr (by omega)))
  obtain ⟨M, k, hM⟩ := FinTM.computesFunInTime_comp c.canonizer_computes hG' hmono
  have e : (rc_g ∘ fun α => (c.decode α).serialize) =
      fun α => serializeK (c.decode α).tm.replayTM := by
    funext α
    rw [Function.comp_apply, rc_g_serialize]
  exact ⟨M, _, e ▸ hM⟩

/-- Replaying any prefix of the stream on the bounded window gives the original branch's
control and output. The stream may be longer than the deadline.

**Proof sketch.** The replay theorem removes the extra choice tape. Input locality then
identifies the run on `x.take t` with the run on `x`, since the prefix has at most `t` bits. -/
private theorem ic_replay_window {k : ℕ} {S : Type} (N : NDTM k Bool S)
    (x s : List Bool) (t r : ℕ) (hs : t ≤ s.length) (hr : r ≤ t) :
    let d := N.replayTM.runFrom
      (NDTM.withChoiceTape (N.initCfg (x.take t)) (FinTM.bufferTape s) 0) r
    let e := N.runWith (s.take r) (N.initCfg x)
    d.state = e.state ∧ d.output = e.output := by
  obtain ⟨p, _, _, replay⟩ := N.replayTM_runFrom (N.initCfg (x.take t)) s r
    (hr.trans hs)
  have locality := N.runWith_initCfg_take x t (s.take r) (by
    rw [List.length_take]
    omega)
  dsimp only
  rw [replay, NDTM.withChoiceTape_state, NDTM.withChoiceTape_output]
  exact ⟨locality.1, locality.2.2.2.2⟩

/-- The replay canonizer can be called through the clean installation interface, with a
cost depending on the code alone. The installed word is the entire replay serialization.

**Proof sketch.** Take the canonizer from its gated statement and feed its computation contract
to the public install-call theorem. Both the argument and its result depend only on the code. -/
private theorem ic_table_call (c : EffectiveNDMachineCode) :
    ∃ (M : FinTM Bool) (entry done : M.State) (cost : List Bool → ℕ), 0 < M.k ∧
      ∀ x α : List Bool, ∃ T ≤ cost α, 0 < T ∧
        (∀ u, 0 < u → u < T →
          (M.tm.runFrom
            (Cfg.ofWords (input := x) entry (stateWord M.k α)) u).state ≠ some done) ∧
        M.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord M.k α)) T =
          Cfg.ofWords done (stateWord M.k (serializeK (c.decode α).tm.replayTM)) := by
  obtain ⟨F, τ, computes⟩ := exists_replayCanonizer c
  obtain ⟨M, entry, done, a, positive, installs⟩ :=
    FinTM.exists_installCallTM F _ τ computes
  exact ⟨M, entry, done,
    fun α => a * (τ α.length + α.length + (serializeK (c.decode α).tm.replayTM).length + 1),
    positive, installs⟩

/-- The installed table and empty-output summary, together with the mirrored initial tapes,
represent the replay machine's start with its entire choice stream on the last mirrored tape.

**Proof sketch.** Assemble the six fields of the public representation equivalence. The replay
start has the nondeterministic machine's initial state and empty output; its work tapes are the
blank initial bank followed by the supplied stream. -/
private theorem ic_replay_rep {k n : ℕ} (N : NDTM k Bool (Fin (n + 1))) (x s : List Bool)
    (d : Cfg (k + 1 + 2) Bool (Σ key, StepBlock.Ph (k + 1) key) x)
    (hin : d.inputPos.val = 1)
    (hbank : ∀ i : Fin (k + 1),
      d.workTapes (Fin.castAdd 2 i) =
        Fin.lastCases (FinTM.bufferTape s) (fun _ _ => none) i ∧
      d.workTapePos (Fin.castAdd 2 i) = Fin.lastCases 0 (fun _ => 0) i)
    (htbl : d.workTapes (StepBlock.tableTape (k + 1)) =
      FinTM.bufferTape (tableBitsK N.replayTM.tr))
    (hsm : d.workTapes (StepBlock.summaryTape (k + 1)) =
      StepBlock.summaryCells none (unaryFin N.q₀))
    (htblp : d.workTapePos (StepBlock.tableTape (k + 1)) = 0)
    (hsmp : d.workTapePos (StepBlock.summaryTape (k + 1)) = 0) :
    StepBlock.Rep N.replayTM.tr
      (NDTM.withChoiceTape (N.initCfg x) (FinTM.bufferTape s) 0) d := by
  apply StepBlock.Rep_iff.mpr
  refine ⟨?_, ?_, htbl, ?_, htblp, hsmp⟩
  · rw [NDTM.withChoiceTape_inputPos, NDTM.initCfg_eq, Cfg.init_inputPos]
    exact Fin.ext hin
  · intro i
    have tapes : (N.initCfg x).workTapes = fun _ _ => none := by
      funext j a
      rw [NDTM.initCfg_eq, Cfg.init_workTapes]
    have heads : (N.initCfg x).workTapePos = fun _ => 0 := by
      funext j
      rw [NDTM.initCfg_eq, Cfg.init_workTapePos]
    obtain ⟨htape, hhead⟩ := hbank i
    refine ⟨?_, ?_⟩
    · funext a
      rw [htape, NDTM.withChoiceTape_workTapes, tapes]
    · rw [hhead, NDTM.withChoiceTape_workTapePos, heads]
  · simpa only [NDTM.withChoiceTape_output, NDTM.withChoiceTape_state, NDTM.initCfg_eq,
      Cfg.init_output, Cfg.init_state, Option.map_some, Option.getD_some,
      StepBlock.outputSummary_nil] using hsm

/-- From a represented replay start, the hosted loop has both time bounds measured against
the original nondeterministic branch. Its exit and summary cell give that branch's halting
status and output, and neither loop exit occurs earlier, for either boundary tag.

**Proof sketch.** Apply the existing hosted-loop contract with the untouched binary counter.
The initial boundary tag is valid even for an empty window. Replay and input locality transfer
both the endpoint semantics and every early-halting hypothesis to the original input. Finally
read the summary cell through the hosted-loop reading theorem. -/
private theorem ic_loop_replay {n : ℕ} (N : NDTM 2 Bool (Fin (n + 1)))
    (x s : List Bool) (t : ℕ) (hs : t ≤ s.length)
    (d : Cfg 5 Bool (Σ key, StepBlock.Ph 3 key) (x.take t))
    (entry : d.state = some (StepBlock.exit 3 true))
    (rel : StepBlock.Rep N.replayTM.tr
      (NDTM.withChoiceTape (N.initCfg (x.take t)) (FinTM.bufferTape s) 0) d)
    (z : List Bool) (p : Fin (z.length + 2)) :
    let start := vhostCfg
      (counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape (Nat.bits t)) 0) true p []
    let branch := N.runWith (s.take t) (N.initCfg x)
    ∃ (T : ℕ) (e : Cfg 5 Bool (Σ key, StepBlock.Ph 3 key) (x.take t))
      (ct' : ℤ → Option Bool) (b' : Bool),
      T ≤ t * (50 * ((tableBitsK N.replayTM.tr).length + 1)) +
        4 * t + 2 * (Nat.bits t).length + 2 ∧
      (∀ r ≤ t, (N.runWith (s.take r) (N.initCfg x)).state = none →
        T ≤ r * (50 * ((tableBitsK N.replayTM.tr).length + 1)) +
          4 * r + 2 * (Nat.bits t).length) ∧
      e.output = d.output ∧
      (StepBlock.hostedLoopTM 3).runFrom start T =
        vhostCfg (counterLoopCfg
          (some (if branch.state.isSome then .done else .escape)) e ct' 0) b' p [] ∧
      ((StepBlock.hostedLoopTM 3).runFrom start T).workTapeSymbols
        (vhostBank (StepBlock.summaryTape 3).castSucc) = StepBlock.outputSummary branch.output ∧
      ∀ u < T, ∀ tag,
        ((StepBlock.hostedLoopTM 3).runFrom start u).state ≠ some (.done, tag) ∧
        ((StepBlock.hostedLoopTM 3).runFrom start u).state ≠ some (.escape, tag) := by
  dsimp only
  let c₀ := NDTM.withChoiceTape (N.initCfg (x.take t)) (FinTM.bufferTape s) 0
  have live : c₀.state ≠ none := by
    rw [NDTM.withChoiceTape_state, NDTM.initCfg_eq, Cfg.init_state]
    exact Option.some_ne_none _
  have tag : FinTM.VirtualTag c₀.inputPos true := by
    rw [FinTM.VirtualTag_iff, NDTM.withChoiceTape_inputPos, NDTM.initCfg_eq, Cfg.init_inputPos]
    constructor
    · intro h
      norm_num at h
    · intro _
      rfl
  have value : Nat.ofDigits 2 ((Nat.bits t).map Bool.toNat) = t :=
    (counterValue_eq _).symm.trans (counterValue_bits t)
  obtain ⟨T, e, ct', b', bound, early, represented, output, _, _, run, cut⟩ :=
    StepBlock.hostedLoopTM_run N.replayTM c₀ live d entry rel (Nat.bits t)
      (FinTM.bufferTape (Nat.bits t)) 0 (by intros; rw [zero_add]) t value true tag p []
  have semantic := ic_replay_window N x s t t hs le_rfl
  have reading := (StepBlock.hostedLoop_read N.replayTM.tr (N.replayTM.runFrom c₀ t)
    e represented
    (if (N.runWith (s.take t) (N.initCfg x)).state.isSome then .done else .escape)
    ct' 0 b' p []).2.2.2
  refine ⟨T, e, ct', b', bound, ?_, output, ?_, ?_, cut⟩
  · intro r hr halted
    apply early r hr
    exact (ic_replay_window N x s t r hs hr).1.trans halted
  · rw [semantic.1] at run
    exact run
  · rw [run, semantic.1]
    exact reading.trans (congrArg StepBlock.outputSummary semantic.2)

/-- The interpreter's final one-step read, with live verdict states. The entry bit records
whether the simulated machine halted; the accepting verdict additionally requires the summary
cell to contain `some true`. This consumer-specific leaf supplies the two live verdicts that
the hosted loop leaves to its caller; it is not another loop or dispatch host. -/
private def ic_verdictTM (K : ℕ) (summary : Fin K) : MultiTapeTM K Bool (Bool ⊕ Bool) where
  q₀ := Sum.inl false
  tr := fun q _ cells =>
    let verdict := match q with
      | Sum.inl halted => halted && decide (cells summary = some true)
      | Sum.inr result => result
    ⟨0, fun _ => (none, 0), none, some (Sum.inr verdict)⟩

/-- The verdict leaf reaches the correct live verdict in exactly one step, before which
neither verdict has been reached. The summary characterization recognizes precisely the
singleton accepting output.

**Proof sketch.** The only strict prefix of one step is the entry configuration, whose state
is in the other sum constructor. For the endpoint use the live-step and action-state equations
and the public characterization of an accepting summary. -/
private theorem ic_verdictTM_run {K : ℕ} (summary : Fin K) {z : List Bool}
    (d : Cfg K Bool (Bool ⊕ Bool) z) (halted : Bool) (out : List Bool)
    (hd : d.state = some (Sum.inl halted))
    (hsummary : d.workTapeSymbols summary = StepBlock.outputSummary out) :
    ((ic_verdictTM K summary).runFrom d 1).state =
      some (Sum.inr (decide (halted = true ∧ out = [true]))) ∧
      ∀ u < 1, ∀ verdict : Bool,
        ((ic_verdictTM K summary).runFrom d u).state ≠ some (Sum.inr verdict) := by
  constructor
  · rw [show 1 = 0 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, MultiTapeTM.step_of_some hd, Action.apply_state]
    simp only [ic_verdictTM, hsummary]
    congr 2
    cases halted <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true,
      false_and, decide_false, true_and, StepBlock.outputSummary_true]
  · intro u hu verdict
    have zero : u = 0 := by omega
    rw [zero, MultiTapeTM.runFrom_zero, hd]
    exact fun h => Sum.noConfusion (Option.some.inj h)

/-- The two phases of the interpreter's loop and final verdict read. -/
private def ic_loopPh : Bool → Type
  | false => CounterLoopState (Σ key, StepBlock.Ph 3 key) × Bool
  | true => Bool ⊕ Bool

/-- Each of the interpreter's two final phases has a finite control type. -/
private instance ic_loopPh_fintype (phase : Bool) : Fintype (ic_loopPh phase) := by
  cases phase <;> dsimp only [ic_loopPh] <;> infer_instance

/-- The existing hosted loop followed by the consumer's one-step verdict leaf. -/
private def ic_loopPiece (phase : Bool) : MultiTapeTM 7 Bool (ic_loopPh phase) :=
  match phase with
  | false => StepBlock.hostedLoopTM 3
  | true => ic_verdictTM 7 (vhostBank (StepBlock.summaryTape 3).castSucc)

/-- The loop's two exits dispatch to the corresponding verdict entry, independently of their
arrival tag. Verdict states stay live; all dispatch is performed by the shared phase host. -/
private def ic_loopRedirect : (phase : Bool) → ic_loopPh phase → Option (Σ i, ic_loopPh i)
  | false, (.done, _) => some ⟨true, Sum.inl false⟩
  | false, (.escape, _) => some ⟨true, Sum.inl true⟩
  | false, _ => none
  | true, Sum.inl _ => none
  | true, Sum.inr result => some ⟨true, Sum.inr result⟩

/-- The interpreter's loop and verdict stages assembled by the public phase host. -/
private def ic_loopHost : MultiTapeTM 7 Bool (Σ i, ic_loopPh i) :=
  phaseHostTM ic_loopPiece ⟨false, (.dec .run, true)⟩ ic_loopRedirect

/-- The loop-to-verdict assembly adds two steps and preserves the first-verdict guarantee.
Both boundary tags and both loop exits are handled by the same machine.

**Proof sketch.** The shared phase-host theorem transports the loop through its first exit,
then performs one silent dispatch to the verdict entry. Its theorem applied to the verdict
leaf transports the final read. Before dispatch all states carry the loop tag; at dispatch
the leaf is still at an entry, so neither live verdict has occurred. -/
private theorem ic_loopHost_run {z : List Bool}
    (d : Cfg 7 Bool (CounterLoopState (Σ key, StepBlock.Ph 3 key) × Bool) z)
    (T : ℕ) (halted tag : Bool) (out : List Bool)
    (exit : ((StepBlock.hostedLoopTM 3).runFrom d T).state =
      some ((if halted then .escape else .done), tag))
    (read : ((StepBlock.hostedLoopTM 3).runFrom d T).workTapeSymbols
      (vhostBank (StepBlock.summaryTape 3).castSucc) = StepBlock.outputSummary out)
    (cut : ∀ u < T, ∀ b,
      ((StepBlock.hostedLoopTM 3).runFrom d u).state ≠ some (.done, b) ∧
      ((StepBlock.hostedLoopTM 3).runFrom d u).state ≠ some (.escape, b)) :
    (ic_loopHost.runFrom (d.mapState (Sigma.mk false)) (T + 2)).state =
      some ⟨true, Sum.inr (decide (halted = true ∧ out = [true]))⟩ ∧
      ∀ u < T + 2, ∀ verdict : Bool,
        (ic_loopHost.runFrom (d.mapState (Sigma.mk false)) u).state ≠
          some ⟨true, Sum.inr verdict⟩ := by
  let e := (StepBlock.hostedLoopTM 3).runFrom d T
  have guard : ∀ u < T, ∀ q,
      ((ic_loopPiece false).runFrom d u).state = some q → ic_loopRedirect false q = none := by
    intro u hu q hq
    rcases q with ⟨q, b⟩
    cases q with
    | dec q => rfl
    | body q => rfl
    | done => exact False.elim ((cut u hu b).1 hq)
    | escape => exact False.elim ((cut u hu b).2 hq)
  have redirect : ic_loopRedirect false ((if halted then .escape else .done), tag) =
      some ⟨true, Sum.inl halted⟩ := by
    cases halted <;> rfl
  obtain ⟨hpre, dispatch⟩ := phaseHostTM_run ic_loopPiece
    ⟨false, (.dec .run, true)⟩ ic_loopRedirect false d e T rfl
    ((if halted then .escape else .done), tag) exit ⟨true, Sum.inl halted⟩ redirect guard
  let leaf : Cfg 7 Bool (Bool ⊕ Bool) z := e.mapState (fun _ => Sum.inl halted)
  have entry : leaf.state = some (Sum.inl halted) := by
    rw [Cfg.mapState_state, exit, Option.map_some]
  have cell : leaf.workTapeSymbols (vhostBank (StepBlock.summaryTape 3).castSucc) =
      StepBlock.outputSummary out := by
    rw [Cfg.workTapeSymbols_eq, Cfg.mapState_workTapes, Cfg.mapState_workTapePos,
      ← Cfg.workTapeSymbols_eq]
    exact read
  obtain ⟨verdict, _⟩ := ic_verdictTM_run
    (vhostBank (StepBlock.summaryTape 3).castSucc) leaf halted out entry cell
  have leafGuard : ∀ u < 1, ∀ q,
      ((ic_loopPiece true).runFrom leaf u).state = some q → ic_loopRedirect true q = none := by
    intro u hu q hq
    have zero : u = 0 := by omega
    rw [zero, MultiTapeTM.runFrom_zero, entry] at hq
    cases Option.some.inj hq
    rfl
  have leafRun := (phaseHostTM_run ic_loopPiece ⟨false, (.dec .run, true)⟩
    ic_loopRedirect true leaf ((ic_loopPiece true).runFrom leaf 1) 1 rfl
    (Sum.inr (decide (halted = true ∧ out = [true]))) verdict
    ⟨true, Sum.inr (decide (halted = true ∧ out = [true]))⟩ rfl leafGuard).1 1 le_rfl
  have seam : e.mapState (fun _ => (⟨true, Sum.inl halted⟩ : Σ i, ic_loopPh i)) =
      leaf.mapState (Sigma.mk true) := by
    apply Cfg.ext <;> (try funext i) <;> (try funext p) <;>
      simp only [leaf, Cfg.mapState_state, Cfg.mapState_inputPos,
        Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Cfg.mapState_output,
        Option.map_map, Function.comp_def]
  constructor
  · change ((phaseHostTM ic_loopPiece ⟨false, (.dec .run, true)⟩ ic_loopRedirect).runFrom
      (d.mapState (Sigma.mk false)) (T + 2)).state = _
    rw [show T + 2 = (T + 1) + 1 by omega, MultiTapeTM.runFrom_add, dispatch]
    have final : ((phaseHostTM ic_loopPiece ⟨false, (.dec .run, true)⟩ ic_loopRedirect).runFrom
        (leaf.mapState (Sigma.mk true)) 1).state =
        some ⟨true, Sum.inr (decide (halted = true ∧ out = [true]))⟩ := by
      rw [leafRun, Cfg.mapState_state, verdict, Option.map_some]
    rw [← seam] at final
    exact final
  · intro u hu result
    by_cases before : u ≤ T
    · change ((phaseHostTM ic_loopPiece ⟨false, (.dec .run, true)⟩ ic_loopRedirect).runFrom
        (d.mapState (Sigma.mk false)) u).state ≠ _
      rw [hpre u before, Cfg.mapState_state]
      cases hs : ((ic_loopPiece false).runFrom d u).state with
      | none => exact Option.noConfusion
      | some q =>
        intro bad
        have impossible := congrArg Sigma.fst (Option.some.inj bad)
        exact Bool.noConfusion impossible
    · have atDispatch : u = T + 1 := by omega
      change ((phaseHostTM ic_loopPiece ⟨false, (.dec .run, true)⟩ ic_loopRedirect).runFrom
        (d.mapState (Sigma.mk false)) u).state ≠ _
      rw [atDispatch, dispatch, Cfg.mapState_state, exit, Option.map_some]
      intro bad
      have impossible := (Sigma.mk.inj (Option.some.inj bad)).2
      cases impossible

/-- Once startup has produced the represented replay start, one fixed finite-control machine
runs the branch and reaches its correct first verdict. The total and prefix costs include the
two final dispatch/read steps.

**Proof sketch.** Use the semantic hosted-loop contract, extract its exit state through the
configuration equations, and apply the loop-to-verdict assembly. Negated liveness is exactly
halting, so the resulting Boolean verdict is the target's acceptance predicate. -/
private theorem ic_replay_tail {n : ℕ} (N : NDTM 2 Bool (Fin (n + 1)))
    (x s : List Bool) (t : ℕ) (hs : t ≤ s.length)
    (d : Cfg 5 Bool (Σ key, StepBlock.Ph 3 key) (x.take t))
    (entry : d.state = some (StepBlock.exit 3 true))
    (rel : StepBlock.Rep N.replayTM.tr
      (NDTM.withChoiceTape (N.initCfg (x.take t)) (FinTM.bufferTape s) 0) d)
    (z : List Bool) (p : Fin (z.length + 2)) :
    let start := vhostCfg
      (counterLoopCfg (some (.dec .run)) d (FinTM.bufferTape (Nat.bits t)) 0) true p []
    let branch := N.runWith (s.take t) (N.initCfg x)
    ∃ T,
      T ≤ t * (50 * ((tableBitsK N.replayTM.tr).length + 1)) +
        4 * t + 2 * (Nat.bits t).length + 4 ∧
      (∀ r ≤ t, (N.runWith (s.take r) (N.initCfg x)).state = none →
        T ≤ r * (50 * ((tableBitsK N.replayTM.tr).length + 1)) +
          4 * r + 2 * (Nat.bits t).length + 2) ∧
      (ic_loopHost.runFrom (start.mapState (Sigma.mk false)) T).state =
        some ⟨true, Sum.inr (decide (branch.state = none ∧ branch.output = [true]))⟩ ∧
      ∀ u < T, ∀ verdict : Bool,
        (ic_loopHost.runFrom (start.mapState (Sigma.mk false)) u).state ≠
          some ⟨true, Sum.inr verdict⟩ := by
  dsimp only
  obtain ⟨T, e, ct', b', bound, early, _, run, summary, cut⟩ :=
    ic_loop_replay N x s t hs d entry rel z p
  let branch := N.runWith (s.take t) (N.initCfg x)
  have state := congrArg Cfg.state run
  rw [vhostCfg_state, counter_cfg_eq _ e, Option.map_some] at state
  have exit : ((StepBlock.hostedLoopTM 3).runFrom
      (vhostCfg (counterLoopCfg (some (.dec .run)) d
        (FinTM.bufferTape (Nat.bits t)) 0) true p []) T).state =
      some ((if !branch.state.isSome then .escape else .done), b') := by
    cases hb : branch.state.isSome <;>
      simpa only [branch, hb, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte] using state
  obtain ⟨correct, first⟩ := ic_loopHost_run _ T (!branch.state.isSome) b' branch.output
    exit summary cut
  refine ⟨T + 2, by omega, ?_, ?_, first⟩
  · intro r hr halted
    have h := early r hr halted
    omega
  · simpa only [Option.not_isSome, Option.isNone_iff_eq_none] using correct

/-- A single per-code constant absorbs both the full-deadline ledger and the early-halting
ledger. Fixed dispatch costs and the serialization layout cost belong in the startup constant.

**Proof sketch.** For the full deadline, bound the binary width and window length by the
deadline. For early halting, bound the window by the input length and bound each coefficient
by the chosen constant. No comparison of the early halting time with the deadline is needed
for the second arithmetic inequality. -/
private theorem ic_time_ledger (a b w L t x r : ℕ) :
    let C := a + b + w + 50 * (L + 1) + 10
    (a + (b + 4) * (Nat.bits t).length + w * (min t x + 1) +
        (50 * (L + 1) + 4) * t + 2 ≤ C * (t + 1)) ∧
      (a + (b + 4) * (Nat.bits t).length + w * (min t x + 1) +
        (50 * (L + 1) + 4) * r ≤ C * (r + x + (Nat.bits t).length + 1)) := by
  dsimp only
  constructor
  · calc
      _ ≤ a + (b + 4) * t + w * (t + 1) + (50 * (L + 1) + 4) * t + 2 := by
        gcongr
        · exact length_bits_le_self t
        · exact min_le_left t x
      _ ≤ _ := by
        ring_nf
        omega
  · calc
      _ ≤ a + (b + 4) * (Nat.bits t).length + w * (x + 1) +
          (50 * (L + 1) + 4) * r := by
        gcongr
        exact min_le_right t x
      _ = a + w + (b + 4) * (Nat.bits t).length + w * x +
          (50 * (L + 1) + 4) * r := by ring
      _ ≤ (a + b + w + 50 * (L + 1) + 10) +
          (a + b + w + 50 * (L + 1) + 10) * (Nat.bits t).length +
          (a + b + w + 50 * (L + 1) + 10) * x +
          (a + b + w + 50 * (L + 1) + 10) * r := by
        gcongr ?_ + ?_ * _ + ?_ * _ + ?_ * _ <;> omega
      _ = _ := by ring

/-- **The interpreter core for nondeterministic codes** `R` (deterministic; shared by the
universal NDTM and the diagonalizer's mid-rung). For every effective nondeterministic scheme
`c` there is one finite machine `R`, uniform over codes, with `K` work tapes, a designated stream
tape `j`, an entry state and two distinct verdict states `accept ≠ reject`, such that for every
code `α` there is a constant `C` with the following property. Start `R` at `entry` on the
native input `z = ⟨⟨bits t, α⟩, x⟩` (input head on its first symbol), with a stream `s` of
length at least `t` on tape `j` from cell `0`, every other tape blank, every head at `0`, and
empty output. Let `e` be the coded machine's branch on `x` along `s.take t`. Then `R` reaches
`accept` if `e` has halted with output exactly `[true]`, and `reject` otherwise, at a time `T`
with no verdict earlier, where:
* `T ≤ C·(t + 1)` in every case, with no `|x|` term;
* `T ≤ C·(t' + |x| + |bits t| + 1)` whenever the branch along `s.take t'` has already halted,
  for `t' ≤ t` (**the prefix clause**: the cost of a branch that halts early is linear in its
  own length, plus the window copy and the counter width).
[AB09, Exercise 2.6, §1.4.1: the universal machine, here for one fixed choice word]

**Proof sketch.** Per-code startup: parse the nested header, leaving `bits t` on a counter
tape; install the replay serialization of `Turing.exists_replayCanonizer` by
`Turing.FinTM.exists_installCallTM` with the unary initial state; copy the input window
`x.take t` onto a buffer by `Turing.exists_inputWindowCopyTM` (cost `O(min(t, |x|) + |bits t|)`)
and rewind it. Then the deterministic clocked interpreter loop at three work tapes, the stream
as the mirrored choice tape: the counter loop over H2's step block hosted by Z1 on the window,
from the replay machine's represented start with the stream installed, over the counter
`bits t` (`Turing.StepBlock.hostedLoopTM_run`, host H2-L in `Build/StepBlockLoop`; the
counter's value is `Turing.counterValue_bits`). Each round is one step of the replay machine and
costs at most a per-code constant (H2's `50·(|table| + 1)`), and the counter costs at most
`4r + 2|bits t|` over `r` rounds; when the simulated machine halts by `t'`, the loop escapes
within `t'·50·(|table| + 1) + 4t' + 2|bits t|` (the contract's early-escape bound), which gives
the prefix clause. The verdict reads H2's output summary at the live exits
(`Turing.StepBlock.hostedLoop_read`). The replay lemma `Turing.NDTM.replayTM_runFrom` identifies
the simulated run with the branch along `s.take t` on the window, and input locality
(`Turing.NDTM.runWith_initCfg_take`) with the branch on `x`.

**Implementation.** `R` is the interpreter startup `Turing.exists_interpreterStartup`, seamed to the
hosted loop embedded silently. The startup runs with the replay serialization's installer and
four passive tapes: the stream, the loop's two banks and the loop's capture. Its eleven phases
are the two header passes, the counter copy, the window copy, the installation and the seam
layout, with their rewinds. At its threshold it leaves `bits t`, the window `x.take t`, the
replay machine's table and its summary on four role tapes, every head at `0`, the passive
tapes as they started, and the input head at its first cell. The loop's entry is read from
these fields, and the join is `Turing.seamCompTM_step` with the startup's first-return cut. -/
theorem exists_ndInterpreterCore (c : EffectiveNDMachineCode) :
    ∃ (K : ℕ) (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (R : MultiTapeTM K Bool Q)
      (j : Fin K) (entry accept reject : Q), accept ≠ reject ∧
      ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ) (s : List Bool), t ≤ s.length →
        let z := pairEncode (pairEncode (Nat.bits t) α) x
        let N := (c.decode α).toFinNDTM
        let start : Cfg K Bool Q z :=
          ⟨some entry, 1, fun i => if i = j then FinTM.bufferTape s else fun _ => none,
            fun _ => 0, []⟩
        let e := N.tm.runWith (s.take t) (N.tm.initCfg x)
        ∃ T, (∀ t' ≤ t, (N.tm.runWith (s.take t') (N.tm.initCfg x)).state = none →
                T ≤ C * (t' + x.length + (Nat.bits t).length + 1)) ∧
          T ≤ C * (t + 1) ∧
          (R.runFrom start T).state =
            some (if e.state = none ∧ e.output = [true] then accept else reject) ∧
          ∀ u < T, (R.runFrom start u).state ≠ some accept ∧
            (R.runFrom start u).state ≠ some reject := by
  classical
  obtain ⟨CI, entryI, doneI, costI, hkI, installs⟩ := ic_table_call c
  obtain ⟨K, QU, instFU, instDU, U, entryU, doneU, ιP, jctr, jwin, jtbl, jsm, A, B,
      hcw, hct, hcs, hwt, hws, hts, hcP, hwP, htP, hsP, startup⟩ :=
    exists_interpreterStartup (fun α => (c.decode α).numStates)
      (fun α => (c.decode α).tm.replayTM) CI entryI doneI costI hkI
      (fun x α => by rw [← serializeK_eq]; exact installs x α) 4
  haveI := instFU
  haveI := instDU
  obtain ⟨js, hjs⟩ : {j : Fin K // j = ιP 0} := ⟨_, rfl⟩
  obtain ⟨jb0, hjb0⟩ : {j : Fin K // j = ιP 1} := ⟨_, rfl⟩
  obtain ⟨jb1, hjb1⟩ : {j : Fin K // j = ιP 2} := ⟨_, rfl⟩
  obtain ⟨capL, hcapL⟩ : {j : Fin K // j = ιP 3} := ⟨_, rfl⟩
  -- The seven loop tapes and the loop capture are distinct.
  have hPP : ∀ a b : Fin 4, a ≠ b → ιP a ≠ ιP b := fun a b h e => h (ιP.injective e)
  have hRP : ∀ j : Fin K, j ∉ Set.range ιP → ∀ i : Fin 4, j ≠ ιP i :=
    fun j h i e => h ⟨i, e.symm⟩
  have hwL : jwin ≠ capL := fun e => hRP jwin hwP 3 (e.trans hcapL)
  have h1L : jb0 ≠ capL := fun e => hPP 1 3 (by decide) (hjb0.symm.trans (e.trans hcapL))
  have h2L : jb1 ≠ capL := fun e => hPP 2 3 (by decide) (hjb1.symm.trans (e.trans hcapL))
  have hsL : js ≠ capL := fun e => hPP 0 3 (by decide) (hjs.symm.trans (e.trans hcapL))
  have htL : jtbl ≠ capL := fun e => hRP jtbl htP 3 (e.trans hcapL)
  have hmL : jsm ≠ capL := fun e => hRP jsm hsP 3 (e.trans hcapL)
  have hcL' : jctr ≠ capL := fun e => hRP jctr hcP 3 (e.trans hcapL)
  let f7 : Fin 7 → Fin K := fun i => if i = 0 then jwin else if i = 1 then jb0 else
    if i = 2 then jb1 else if i = 3 then js else if i = 4 then jtbl else if i = 5 then jsm else jctr
  have hf7 : Function.Injective f7 := by
    have d01 : jwin ≠ jb0 := fun e => hRP jwin hwP 1 (e.trans hjb0)
    have d02 : jwin ≠ jb1 := fun e => hRP jwin hwP 2 (e.trans hjb1)
    have d03 : jwin ≠ js := fun e => hRP jwin hwP 0 (e.trans hjs)
    have d04 : jwin ≠ jtbl := hwt
    have d05 : jwin ≠ jsm := hws
    have d06 : jwin ≠ jctr := hcw.symm
    have d12 : jb0 ≠ jb1 := fun e => hPP 1 2 (by decide) (hjb0.symm.trans (e.trans hjb1))
    have d13 : jb0 ≠ js := fun e => hPP 1 0 (by decide) (hjb0.symm.trans (e.trans hjs))
    have d14 : jb0 ≠ jtbl := fun e => hRP jtbl htP 1 (e.symm.trans hjb0)
    have d15 : jb0 ≠ jsm := fun e => hRP jsm hsP 1 (e.symm.trans hjb0)
    have d16 : jb0 ≠ jctr := fun e => hRP jctr hcP 1 (e.symm.trans hjb0)
    have d23 : jb1 ≠ js := fun e => hPP 2 0 (by decide) (hjb1.symm.trans (e.trans hjs))
    have d24 : jb1 ≠ jtbl := fun e => hRP jtbl htP 2 (e.symm.trans hjb1)
    have d25 : jb1 ≠ jsm := fun e => hRP jsm hsP 2 (e.symm.trans hjb1)
    have d26 : jb1 ≠ jctr := fun e => hRP jctr hcP 2 (e.symm.trans hjb1)
    have d34 : js ≠ jtbl := fun e => hRP jtbl htP 0 (e.symm.trans hjs)
    have d35 : js ≠ jsm := fun e => hRP jsm hsP 0 (e.symm.trans hjs)
    have d36 : js ≠ jctr := fun e => hRP jctr hcP 0 (e.symm.trans hjs)
    have d45 : jtbl ≠ jsm := hts
    have d46 : jtbl ≠ jctr := hct.symm
    have d56 : jsm ≠ jctr := hcs.symm
    intro a b h
    fin_cases a <;> fin_cases b <;> simp only [f7, Fin.isValue] at h ⊢ <;>
      first
      | rfl
      | exact absurd h d01
      | exact absurd h.symm d01
      | exact absurd h d02
      | exact absurd h.symm d02
      | exact absurd h d03
      | exact absurd h.symm d03
      | exact absurd h d04
      | exact absurd h.symm d04
      | exact absurd h d05
      | exact absurd h.symm d05
      | exact absurd h d06
      | exact absurd h.symm d06
      | exact absurd h d12
      | exact absurd h.symm d12
      | exact absurd h d13
      | exact absurd h.symm d13
      | exact absurd h d14
      | exact absurd h.symm d14
      | exact absurd h d15
      | exact absurd h.symm d15
      | exact absurd h d16
      | exact absurd h.symm d16
      | exact absurd h d23
      | exact absurd h.symm d23
      | exact absurd h d24
      | exact absurd h.symm d24
      | exact absurd h d25
      | exact absurd h.symm d25
      | exact absurd h d26
      | exact absurd h.symm d26
      | exact absurd h d34
      | exact absurd h.symm d34
      | exact absurd h d35
      | exact absurd h.symm d35
      | exact absurd h d36
      | exact absurd h.symm d36
      | exact absurd h d45
      | exact absurd h.symm d45
      | exact absurd h d46
      | exact absurd h.symm d46
      | exact absurd h d56
      | exact absurd h.symm d56
  let ι₇ : Fin 7 ↪ Fin K := ⟨f7, hf7⟩
  have hι₇0 : ι₇ 0 = jwin := rfl
  have hι₇1 : ι₇ 1 = jb0 := rfl
  have hι₇2 : ι₇ 2 = jb1 := rfl
  have hι₇3 : ι₇ 3 = js := rfl
  have hι₇4 : ι₇ 4 = jtbl := rfl
  have hι₇5 : ι₇ 5 = jsm := rfl
  have hι₇6 : ι₇ 6 = jctr := rfl
  let A₁₂ := embedSilentTM ι₇ capL ic_loopHost
  let R := seamCompTM U doneU A₁₂ ⟨false, (.dec .run, true)⟩
  refine ⟨K, _, inferInstance, inferInstance, R, js, Sum.inl entryU,
    Sum.inr ⟨true, Sum.inr true⟩, Sum.inr ⟨true, Sum.inr false⟩, ?_, ?_⟩
  · intro hcontra
    injection hcontra with h1
    injection h1 with h1a h1b
    exact Bool.noConfusion (Sum.inr.inj h1b)
  intro α
  refine ⟨(costI α + A * (α.length + (pairEncode (c.decode α).numStates.bits
      (unaryFin (c.decode α).tm.replayTM.q₀ ++
        tableBitsK (c.decode α).tm.replayTM.tr)).length + 1) +
      B + 5) + B + B + 50 * ((tableBitsK (c.decode α).tm.replayTM.tr).length + 1) + 10, ?_⟩
  intro x t s hs
  dsimp only
  simp only [CodeNDTM.toFinNDTM_tm, CodeNDTM.toFinNDTM_k, CodeNDTM.toFinNDTM_State]
  set tapes₀ : Fin K → ℤ → Option Bool :=
    fun i => if i = js then FinTM.bufferTape s else fun _ => none with htapes₀
  have hP0 : ∀ j, j ∉ Set.range ιP → tapes₀ j = fun _ => none := by
    intro j hj
    have hne : j ≠ js := fun e => hj ⟨0, (e.trans hjs).symm⟩
    rw [htapes₀]
    exact if_neg hne
  obtain ⟨T, hT, hst, hcut, hfields⟩ := startup α x t tapes₀ hP0
  set start : Cfg K Bool QU (pairEncode (pairEncode (Nat.bits t) α) x) :=
    ⟨some entryU, 1, tapes₀, fun _ => 0, []⟩ with hstartdef
  set e := U.runFrom start T with he
  dsimp only at hfields
  obtain ⟨he₁₁in, he₁₁out, hctr1, hctr2, hwin₁₁, he₁₁poswin, htbl1, htbl2, hsm1, hsm2, hpas⟩ :=
    hfields
  have hctr₁₁ : e.workTapes jctr = FinTM.bufferTape (Nat.bits t) ∧ e.workTapePos jctr = 0 :=
    ⟨hctr1, hctr2⟩
  have htbl₁₁ : e.workTapes jtbl = FinTM.bufferTape (tableBitsK (c.decode α).tm.replayTM.tr) ∧
      e.workTapePos jtbl = 0 := ⟨htbl1, htbl2⟩
  have hsm₁₁ : e.workTapes jsm =
      StepBlock.summaryCells none (unaryFin (c.decode α).tm.replayTM.q₀) ∧
      e.workTapePos jsm = 0 := ⟨hsm1, hsm2⟩
  -- The stream, the two loop banks and the loop capture: the startup's passive tapes.
  have hstream : e.workTapes js = FinTM.bufferTape s ∧ e.workTapePos js = 0 := by
    obtain ⟨h1, h2⟩ := hpas 0
    rw [← hjs] at h1 h2
    refine ⟨?_, h2⟩
    rw [h1, htapes₀]
    exact if_pos rfl
  have hpasblank : ∀ (j : Fin K) (i : Fin 4), j = ιP i → i ≠ 0 →
      e.workTapes j = (fun _ => none) ∧ e.workTapePos j = 0 := by
    intro j i hji hi0
    obtain ⟨h1, h2⟩ := hpas i
    rw [← hji] at h1 h2
    refine ⟨?_, h2⟩
    have hne : j ≠ js := fun e => hPP i 0 hi0 (hji.symm.trans (e.trans hjs))
    rw [h1, htapes₀]
    exact if_neg hne
  have hb0 := hpasblank jb0 1 hjb0 (by decide)
  have hb1 := hpasblank jb1 2 hjb1 (by decide)
  have hcL := hpasblank capL 3 hcapL (by decide)
  -- Phase 12: the loop entry. The virtual five-tape configuration of the represented start.
  set dstep : Cfg 5 Bool (Σ key, StepBlock.Ph 3 key) (x.take t) :=
    ⟨some (StepBlock.exit 3 true), 1,
      fun i => if i.val = 2 then FinTM.bufferTape s
        else if i.val = 3 then FinTM.bufferTape (tableBitsK (c.decode α).tm.replayTM.tr)
        else if i.val = 4 then StepBlock.summaryCells none (unaryFin (c.decode α).tm.q₀)
        else fun _ => none,
      fun _ => 0, []⟩ with hdstep
  have hrel : StepBlock.Rep (c.decode α).tm.replayTM.tr
      (NDTM.withChoiceTape ((c.decode α).tm.initCfg (x.take t)) (FinTM.bufferTape s) 0)
      dstep := by
    refine ic_replay_rep (c.decode α).tm (x.take t) s dstep (Fin.val_one _) ?_ ?_ ?_ rfl rfl
    · intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · constructor
        · simp only [hdstep, Fin.lastCases_last, Fin.coe_castAdd, Fin.val_last]
          norm_num
        · simp only [hdstep, Fin.lastCases_last]
      · have hlt := i'.isLt
        constructor
        · simp only [hdstep, Fin.lastCases_castSucc, Fin.coe_castAdd, Fin.coe_castSucc]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        · simp only [hdstep, Fin.lastCases_castSucc]
    · simp only [hdstep, StepBlock.tableTape_eq, Fin.coe_natAdd, Fin.val_zero]
      norm_num
    · simp only [hdstep, StepBlock.summaryTape_eq, Fin.coe_natAdd, Fin.val_one]
      norm_num
  obtain ⟨TLoop, hTLoopFull, hTLoopEarly, hLoopSt, hLoopCut⟩ :=
    ic_replay_tail ((c.decode α).tm) x s t hs dstep rfl hrel
      (pairEncode (pairEncode (Nat.bits t) α) x) e.inputPos
  -- The counter-loop configuration's fields, read through its public layout.
  have hcl_tapes : ∀ i : Fin 6, (counterLoopCfg (some (CounterLoopState.dec FlagPhase.run))
      dstep (FinTM.bufferTape (Nat.bits t)) 0).workTapes i =
      Fin.lastCases (FinTM.bufferTape (Nat.bits t)) dstep.workTapes i := by
    intro i
    rw [counter_cfg_eq]
  have hcl_pos : ∀ i : Fin 6, (counterLoopCfg (some (CounterLoopState.dec FlagPhase.run))
      dstep (FinTM.bufferTape (Nat.bits t)) 0).workTapePos i =
      Fin.lastCases 0 dstep.workTapePos i := by
    intro i
    rw [counter_cfg_eq]
  have hcl_in : (counterLoopCfg (some (CounterLoopState.dec FlagPhase.run))
      dstep (FinTM.bufferTape (Nat.bits t)) 0).inputPos = dstep.inputPos := by
    rw [counter_cfg_eq]
  have hcl_out : (counterLoopCfg (some (CounterLoopState.dec FlagPhase.run))
      dstep (FinTM.bufferTape (Nat.bits t)) 0).output = dstep.output := by
    rw [counter_cfg_eq]
  have hcl_state : (counterLoopCfg (some (CounterLoopState.dec FlagPhase.run))
      dstep (FinTM.bufferTape (Nat.bits t)) 0).state =
      some (CounterLoopState.dec FlagPhase.run) := by
    rw [counter_cfg_eq]
  -- The hosted start, embedded: the loop junction.
  have hlhs12t : ∀ j, (e.mapState
      (fun _ => (⟨false, (CounterLoopState.dec FlagPhase.run, true)⟩ :
        Σ i, ic_loopPh i))).workTapes j = e.workTapes j := by
    intro j
    funext a
    rw [Cfg.mapState_workTapes]
  have hlhs12p : ∀ j, (e.mapState
      (fun _ => (⟨false, (CounterLoopState.dec FlagPhase.run, true)⟩ :
        Σ i, ic_loopPh i))).workTapePos j = e.workTapePos j := by
    intro j
    rw [Cfg.mapState_workTapePos]
  have hcapL7 : capL ∉ Set.range ι₇ := by
    rintro ⟨i, hi⟩
    fin_cases i
    · exact hwL hi
    · exact h1L hi
    · exact h2L hi
    · exact hsL hi
    · exact htL hi
    · exact hmL hi
    · exact hcL' hi
  have hfv2 : ((2 : Fin 5)).val = 2 := rfl
  have hfv3 : ((3 : Fin 5)).val = 3 := rfl
  have hfv4 : ((4 : Fin 5)).val = 4 := rfl
  have hjunc₁₂ : e.mapState
      (fun _ => (⟨false, (CounterLoopState.dec FlagPhase.run, true)⟩ : Σ i, ic_loopPh i)) =
      embedSilentCfg ι₇ capL e.workTapes e.workTapePos [] []
        ((vhostCfg (counterLoopCfg (some (CounterLoopState.dec FlagPhase.run)) dstep
          (FinTM.bufferTape (Nat.bits t)) 0) true e.inputPos []).mapState
          (Sigma.mk false)) := by
    have hnotr : ∀ j : Fin K,
        j ≠ jwin → j ≠ jb0 → j ≠ jb1 → j ≠ js → j ≠ jtbl → j ≠ jsm →
        j ≠ jctr → j ∉ Set.range ι₇ := by
      intro j n0 n1 n2 n3 n4 n5 n6
      rintro ⟨i, rfl⟩
      fin_cases i
      · exact n0 rfl
      · exact n1 rfl
      · exact n2 rfl
      · exact n3 rfl
      · exact n4 rfl
      · exact n5 rfl
      · exact n6 rfl
    apply Cfg.ext
    · rw [Cfg.mapState_state, embedSilentCfg_state, Cfg.mapState_state,
        vhostCfg_state, hcl_state, hst]
      rfl
    · have hl : (e.mapState
          (fun _ => (⟨false, (CounterLoopState.dec FlagPhase.run, true)⟩ :
            Σ i, ic_loopPh i))).inputPos = e.inputPos := by
        rw [Cfg.mapState_inputPos]
      rw [hl]
      conv_rhs => rw [embedSilentCfg_inputPos, Cfg.mapState_inputPos, vhostCfg_inputPos]
    · funext j q
      rw [hlhs12t j]
      by_cases h0 : j = jwin
      · rw [h0, hwin₁₁, ← hι₇0, embedSilentCfg_selected_tape, Cfg.mapState_workTapes,
          vhostCfg_workTapes,
          show (0 : Fin 7) = Fin.castAdd 6 (0 : Fin 1) from by decide, Fin.addCases_left]
      · by_cases h1 : j = jb0
        · rw [h1, hb0.1, ← hι₇1, embedSilentCfg_selected_tape,
            Cfg.mapState_workTapes, vhostCfg_workTapes,
            show (1 : Fin 7) = Fin.natAdd 1 (0 : Fin 6) from by decide, Fin.addCases_right,
            hcl_tapes, show (0 : Fin 6) = Fin.castSucc (0 : Fin 5) from by decide,
            Fin.lastCases_castSucc, hdstep]
          norm_num
        · by_cases h2 : j = jb1
          · rw [h2, hb1.1, ← hι₇2,
              embedSilentCfg_selected_tape,
              Cfg.mapState_workTapes, vhostCfg_workTapes,
              show (2 : Fin 7) = Fin.natAdd 1 (1 : Fin 6) from by decide, Fin.addCases_right,
              hcl_tapes, show (1 : Fin 6) = Fin.castSucc (1 : Fin 5) from by decide,
              Fin.lastCases_castSucc, hdstep]
            norm_num
          · by_cases h3 : j = js
            · rw [h3, hstream.1, ← hι₇3, embedSilentCfg_selected_tape,
                Cfg.mapState_workTapes, vhostCfg_workTapes,
                show (3 : Fin 7) = Fin.natAdd 1 (2 : Fin 6) from by decide, Fin.addCases_right,
                hcl_tapes, show (2 : Fin 6) = Fin.castSucc (2 : Fin 5) from by decide,
                Fin.lastCases_castSucc, hdstep]
              norm_num
            · by_cases h4 : j = jtbl
              · rw [h4, htbl₁₁.1, ← hι₇4, embedSilentCfg_selected_tape,
                  Cfg.mapState_workTapes, vhostCfg_workTapes,
                  show (4 : Fin 7) = Fin.natAdd 1 (3 : Fin 6) from by decide,
                  Fin.addCases_right, hcl_tapes,
                  show (3 : Fin 6) = Fin.castSucc (3 : Fin 5) from by decide,
                  Fin.lastCases_castSucc, hdstep]
                norm_num
              · by_cases h5 : j = jsm
                · rw [h5, hsm₁₁.1, NDTM.replayTM_q₀, ← hι₇5,
                    embedSilentCfg_selected_tape,
                    Cfg.mapState_workTapes, vhostCfg_workTapes,
                    show (5 : Fin 7) = Fin.natAdd 1 (4 : Fin 6) from by decide,
                    Fin.addCases_right, hcl_tapes,
                    show (4 : Fin 6) = Fin.castSucc (4 : Fin 5) from by decide,
                    Fin.lastCases_castSucc, hdstep]
                  norm_num
                · by_cases h6 : j = jctr
                  · rw [h6, hctr₁₁.1, ← hι₇6, embedSilentCfg_selected_tape,
                      Cfg.mapState_workTapes, vhostCfg_workTapes,
                      show (6 : Fin 7) = Fin.natAdd 1 (5 : Fin 6) from by decide,
                      Fin.addCases_right, hcl_tapes,
                      show (5 : Fin 6) = Fin.last 5 from by decide, Fin.lastCases_last]
                  · by_cases hcap : j = capL
                    · rw [hcap, hcL.1,
                        (embedSilentCfg_cap ι₇ capL hcapL7 e.workTapes e.workTapePos
                          [] [] _).1, Cfg.mapState_output, vhostCfg_output, hcl_out, hdstep]
                      simp only [List.nil_append, FinTM.bufferTape_nil]
                    · rw [(embedSilentCfg_unselected ι₇ capL e.workTapes
                        e.workTapePos
                        [] [] _ j (hnotr j h0 h1 h2 h3 h4 h5 h6) hcap).1]
    · funext j
      rw [hlhs12p j]
      by_cases h0 : j = jwin
      · rw [h0, he₁₁poswin, ← hι₇0, embedSilentCfg_selected_pos, Cfg.mapState_workTapePos,
          vhostCfg_workTapePos,
          show (0 : Fin 7) = Fin.castAdd 6 (0 : Fin 1) from by decide, Fin.addCases_left,
          hcl_in, hdstep]
        show (0 : ℤ) = 1 - 1
        ring
      · by_cases h1 : j = jb0
        · rw [h1, hb0.2, ← hι₇1, embedSilentCfg_selected_pos,
            Cfg.mapState_workTapePos, vhostCfg_workTapePos,
            show (1 : Fin 7) = Fin.natAdd 1 (0 : Fin 6) from by decide, Fin.addCases_right,
            hcl_pos, show (0 : Fin 6) = Fin.castSucc (0 : Fin 5) from by decide,
            Fin.lastCases_castSucc, hdstep]
        · by_cases h2 : j = jb1
          · rw [h2, hb1.2, ← hι₇2,
              embedSilentCfg_selected_pos,
              Cfg.mapState_workTapePos, vhostCfg_workTapePos,
              show (2 : Fin 7) = Fin.natAdd 1 (1 : Fin 6) from by decide, Fin.addCases_right,
              hcl_pos, show (1 : Fin 6) = Fin.castSucc (1 : Fin 5) from by decide,
              Fin.lastCases_castSucc, hdstep]
          · by_cases h3 : j = js
            · rw [h3, hstream.2, ← hι₇3, embedSilentCfg_selected_pos,
                Cfg.mapState_workTapePos, vhostCfg_workTapePos,
                show (3 : Fin 7) = Fin.natAdd 1 (2 : Fin 6) from by decide, Fin.addCases_right,
                hcl_pos, show (2 : Fin 6) = Fin.castSucc (2 : Fin 5) from by decide,
                Fin.lastCases_castSucc, hdstep]
            · by_cases h4 : j = jtbl
              · rw [h4, htbl₁₁.2, ← hι₇4, embedSilentCfg_selected_pos,
                  Cfg.mapState_workTapePos, vhostCfg_workTapePos,
                  show (4 : Fin 7) = Fin.natAdd 1 (3 : Fin 6) from by decide,
                  Fin.addCases_right, hcl_pos,
                  show (3 : Fin 6) = Fin.castSucc (3 : Fin 5) from by decide,
                  Fin.lastCases_castSucc, hdstep]
              · by_cases h5 : j = jsm
                · rw [h5, hsm₁₁.2, ← hι₇5, embedSilentCfg_selected_pos,
                    Cfg.mapState_workTapePos, vhostCfg_workTapePos,
                    show (5 : Fin 7) = Fin.natAdd 1 (4 : Fin 6) from by decide,
                    Fin.addCases_right, hcl_pos,
                    show (4 : Fin 6) = Fin.castSucc (4 : Fin 5) from by decide,
                    Fin.lastCases_castSucc, hdstep]
                · by_cases h6 : j = jctr
                  · rw [h6, hctr₁₁.2, ← hι₇6, embedSilentCfg_selected_pos,
                      Cfg.mapState_workTapePos, vhostCfg_workTapePos,
                      show (6 : Fin 7) = Fin.natAdd 1 (5 : Fin 6) from by decide,
                      Fin.addCases_right, hcl_pos,
                      show (5 : Fin 6) = Fin.last 5 from by decide, Fin.lastCases_last]
                  · by_cases hcap : j = capL
                    · rw [hcap, hcL.2,
                        (embedSilentCfg_cap ι₇ capL hcapL7 e.workTapes e.workTapePos
                          [] [] _).2, Cfg.mapState_output, vhostCfg_output, hcl_out, hdstep]
                      simp only [List.nil_append, List.length_nil, Nat.cast_zero]
                    · rw [(embedSilentCfg_unselected ι₇ capL e.workTapes
                        e.workTapePos
                        [] [] _ j (hnotr j h0 h1 h2 h3 h4 h5 h6) hcap).2]
    · rw [Cfg.mapState_output, embedSilentCfg_output]
      exact he₁₁out
  -- The final seam: the embedded hosted loop, its verdict, and its first arrival.
  have hA12 := embedSilentTM_runFrom ι₇ capL hcapL7 ic_loopHost e.workTapes
    e.workTapePos
    [] [] ((vhostCfg (counterLoopCfg (some (CounterLoopState.dec FlagPhase.run)) dstep
      (FinTM.bufferTape (Nat.bits t)) 0) true e.inputPos []).mapState (Sigma.mk false))
  have h₂12 : (embedSilentTM ι₇ capL ic_loopHost).runFrom
      (e.mapState
        (fun _ => (⟨false, (CounterLoopState.dec FlagPhase.run, true)⟩ : Σ i, ic_loopPh i)))
      TLoop =
      embedSilentCfg ι₇ capL e.workTapes e.workTapePos [] []
        (ic_loopHost.runFrom ((vhostCfg (counterLoopCfg
          (some (CounterLoopState.dec FlagPhase.run)) dstep
          (FinTM.bufferTape (Nat.bits t)) 0) true e.inputPos []).mapState (Sigma.mk false))
          TLoop) := by
    rw [hjunc₁₂]
    exact hA12 TLoop
  obtain ⟨sRrun, sRst, sRcut⟩ := seamCompTM_step U doneU
    (embedSilentTM ι₇ capL ic_loopHost)
    (⟨false, (CounterLoopState.dec FlagPhase.run, true)⟩ : Σ i, ic_loopPh i) _
    he.symm hst hcut h₂12
    (by rw [embedSilentCfg_state]; exact hLoopSt)
    (by
      intro u hu
      rw [hjunc₁₂, hA12 u, embedSilentCfg_state]
      exact hLoopCut u hu _)
  -- The target's start is the composite's start.
  have hstart : (⟨some (Sum.inl entryU), 1, tapes₀, fun _ => 0, []⟩ :
      Cfg K Bool (QU ⊕ (Σ i, ic_loopPh i)) (pairEncode (pairEncode (Nat.bits t) α) x)) =
      start.mapState Sum.inl := by
    apply Cfg.ext
    · rw [Cfg.mapState_state]
      rfl
    · rw [Cfg.mapState_inputPos]
    · funext j q
      rw [Cfg.mapState_workTapes]
    · funext j
      rw [Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output]
  -- The time: the startup's bound, the seam's step and the loop's.
  have hT' : T ≤ costI α + A * (α.length + (pairEncode (c.decode α).numStates.bits
      (unaryFin (c.decode α).tm.replayTM.q₀ ++
        tableBitsK (c.decode α).tm.replayTM.tr)).length + 1) +
      B * (Nat.bits t).length + B * min t x.length + B := by
    have h := hT
    rw [Nat.mul_add B, Nat.mul_add B, Nat.mul_one] at h
    omega
  refine ⟨T + 1 + TLoop, ?_, ?_, ?_, ?_⟩
  · -- the prefix clause
    intro t' ht' hhalt
    have hE := hTLoopEarly t' ht' hhalt
    refine le_trans ?_ (ic_time_ledger (costI α + A * (α.length + (pairEncode
      (c.decode α).numStates.bits (unaryFin (c.decode α).tm.replayTM.q₀ ++
        tableBitsK (c.decode α).tm.replayTM.tr)).length + 1) + B + 5) B B
      ((tableBitsK (c.decode α).tm.replayTM.tr).length) t x.length t').2
    have hexp : (costI α + A * (α.length + (pairEncode (c.decode α).numStates.bits
        (unaryFin (c.decode α).tm.replayTM.q₀ ++
          tableBitsK (c.decode α).tm.replayTM.tr)).length + 1) + B + 5) +
        (B + 4) * (Nat.bits t).length + B * (min t x.length + 1) +
        (50 * ((tableBitsK (c.decode α).tm.replayTM.tr).length + 1) + 4) * t' =
        costI α + A * (α.length + (pairEncode (c.decode α).numStates.bits
          (unaryFin (c.decode α).tm.replayTM.q₀ ++
            tableBitsK (c.decode α).tm.replayTM.tr)).length + 1) + B + 5 +
        B * (Nat.bits t).length + 4 * (Nat.bits t).length + B * min t x.length + B +
        t' * (50 * ((tableBitsK (c.decode α).tm.replayTM.tr).length + 1)) + 4 * t' := by
      ring
    rw [hexp]
    omega
  · -- the total clause
    refine le_trans ?_ (ic_time_ledger (costI α + A * (α.length + (pairEncode
      (c.decode α).numStates.bits (unaryFin (c.decode α).tm.replayTM.q₀ ++
        tableBitsK (c.decode α).tm.replayTM.tr)).length + 1) + B + 5) B B
      ((tableBitsK (c.decode α).tm.replayTM.tr).length) t x.length 0).1
    have hexp : (costI α + A * (α.length + (pairEncode (c.decode α).numStates.bits
        (unaryFin (c.decode α).tm.replayTM.q₀ ++
          tableBitsK (c.decode α).tm.replayTM.tr)).length + 1) + B + 5) +
        (B + 4) * (Nat.bits t).length + B * (min t x.length + 1) +
        (50 * ((tableBitsK (c.decode α).tm.replayTM.tr).length + 1) + 4) * t + 2 =
        costI α + A * (α.length + (pairEncode (c.decode α).numStates.bits
          (unaryFin (c.decode α).tm.replayTM.q₀ ++
            tableBitsK (c.decode α).tm.replayTM.tr)).length + 1) + B + 5 +
        B * (Nat.bits t).length + 4 * (Nat.bits t).length + B * min t x.length + B +
        t * (50 * ((tableBitsK (c.decode α).tm.replayTM.tr).length + 1)) + 4 * t + 2 := by
      ring
    rw [hexp]
    omega
  · -- the verdict
    rw [hstart, sRrun, Cfg.mapState_state, embedSilentCfg_state, hLoopSt, Option.map_some]
    by_cases hP : ((c.decode α).tm.runWith (s.take t) ((c.decode α).tm.initCfg x)).state =
        none ∧ ((c.decode α).tm.runWith (s.take t) ((c.decode α).tm.initCfg x)).output = [true]
    · simp only [hP, and_self, decide_true, if_true]
    · simp only [hP, decide_false, if_false]
  · -- no earlier verdict, for either verdict state
    intro u hu
    have hno : ∀ v : Bool,
        (R.runFrom (⟨some (Sum.inl entryU), 1, tapes₀, fun _ => 0, []⟩ :
          Cfg K Bool (QU ⊕ (Σ i, ic_loopPh i)) (pairEncode (pairEncode (Nat.bits t) α) x))
          u).state ≠ some (Sum.inr ⟨true, Sum.inr v⟩) := by
      intro v
      rw [hstart]
      rcases (by
        rcases Nat.lt_or_ge u (T + 1) with hc | hc
        · exact Or.inl (by omega)
        · exact Or.inr ⟨u - (T + 1), by omega, by omega⟩ :
        u ≤ T ∨ ∃ r, r < TLoop ∧ u = T + 1 + r) with hle | ⟨r, hr, rfl⟩
      · have hseg := seamCompTM_runFrom_left U doneU
          (embedSilentTM ι₇ capL ic_loopHost)
          (⟨false, (CounterLoopState.dec FlagPhase.run, true)⟩ : Σ i, ic_loopPh i)
          hcut u hle
        rw [hseg, Cfg.mapState_state]
        intro hbad
        obtain ⟨q, -, heq⟩ := Option.map_eq_some_iff.mp hbad
        exact Sum.noConfusion heq
      · have hseg := seamCompTM_runFrom_right U doneU
          (embedSilentTM ι₇ capL ic_loopHost)
          (⟨false, (CounterLoopState.dec FlagPhase.run, true)⟩ : Σ i, ic_loopPh i)
          he.symm hst hcut r
        rw [hseg, hjunc₁₂, hA12 r, Cfg.mapState_state, embedSilentCfg_state]
        intro hbad
        obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp hbad
        exact hLoopCut r hr v (hq.trans (congrArg some (Sum.inr.inj heq)))
    exact ⟨hno true, hno false⟩

end Turing
