/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.CodeParser

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-code formats

The shared record and table parser layer for fixed machine serializations.
This factors the one- and two-work-tape constructions of [AB09, §1.4].

## Main definitions

* `Turing.CodeFormat` — a table grammar, its laws and its fallback.
* `Turing.actionBitsK` / `Turing.codeReadActionK` — records for any work-tape count.
* `Turing.CodeTable2` — the shared 27-record two-work-tape table.
* `Turing.oneTapeFormat` — the one-work-tape instance and public decoder wrappers.

## Main results

* `Turing.CodeFormat.decode_serialize_pad` — padded decoding recovers the machine.
* `Turing.CodeFormat.canonical_eq` — scanning computes its canonical serialization.
* `Turing.CodeFormat.numStates_decode_le` — the guarded decoded-size bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing


/-! ## Transition records -/

/-- The serialization of a transition record lists the input move, each work-tape write
and move in tape order, the output, and the successor state. [AB09, §1.4] -/
def actionBitsK {k n : ℕ} (a : Action k Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++
    (List.finRange k).flatMap
      (fun i => optOptBoolBits (a.workTapes i).1 ++ signBits (a.workTapes i).2) ++
    optBoolBits a.output ++ optStateBits a.state

/-- Read an optional work-tape write and its head move. [AB09, §1.4] -/
def codeReadWork (xs : List Bool) :
    Option ((Option (Option Bool) × SignType) × List Bool) := do
  let (wr, xs) ← codeReadWrite xs
  let (wm, xs) ← codeReadSign xs
  pure ((wr, wm), xs)

/-- Read a transition record with a vector of `k` work-tape actions. [AB09, §1.4] -/
def codeReadActionK (k n : ℕ) (xs : List Bool) :
    Option (Action k Bool (Fin (n + 1)) × List Bool) := do
  let (im, xs) ← codeReadSign xs
  let (ws, xs) ← codeReadVec codeReadWork k xs
  let (out, xs) ← codeReadOutput xs
  let (q, xs) ← codeReadState (n + 1) xs
  pure (⟨im, ws, out, q⟩, xs)

/-- Skip a work-tape write and move, enforcing their field grammar. [AB09, §1.4] -/
def codeSkipWork (xs : List Bool) : Option (List Bool) :=
  (codeSkipPair (fun _ _ => true) xs).bind (codeSkipPair (fun a b => a || !b))

/-- Skip a transition record for `k` work tapes, checking the successor state bound. [AB09, §1.4] -/
def codeSkipActionK (k n : ℕ) (xs : List Bool) : Option (List Bool) := do
  let xs ← codeSkipPair (fun a b => a || !b) xs
  let xs ← codeSkipRepeat codeSkipWork k xs
  let xs ← codeSkipPair (fun a b => a || !b) xs
  codeSkipState (n + 1) xs

/-- Reading a serialized work-tape action recovers it and leaves the suffix untouched. [AB09, §1.4] -/
lemma codeReadWork_append (p : Option (Option Bool) × SignType) (xs : List Bool) :
    codeReadWork ((optOptBoolBits p.1 ++ signBits p.2) ++ xs) = some (p, xs) := by
  rcases p with ⟨wr, wm⟩
  simp only [codeReadWork, List.append_assoc, codeReadWrite_append, codeReadSign_append,
    bind, Option.bind, pure]

/-- Reading a serialized transition recovers it and leaves the suffix untouched. [AB09, §1.4] -/
lemma codeReadActionK_append {k n : ℕ} (a : Action k Bool (Fin (n + 1))) (xs : List Bool) :
    codeReadActionK k n (actionBitsK a ++ xs) = some (a, xs) := by
  rcases a with ⟨im, ws, out, q⟩
  have hv : ∀ ys, codeReadVec codeReadWork k
      ((List.finRange k).flatMap (fun i => optOptBoolBits (ws i).1 ++ signBits (ws i).2) ++ ys) =
        some (ws, ys) :=
    codeReadVec_append codeReadWork (fun p => optOptBoolBits p.1 ++ signBits p.2)
      codeReadWork_append k ws
  simp only [actionBitsK, List.append_assoc, codeReadActionK, codeReadSign_append, hv,
    codeReadOutput_append, codeReadState_append, bind, Option.bind, pure]

/-- A successful work-tape read consumes exactly the serialization of its result. [AB09, §1.4] -/
lemma codeReadWork_sound (xs : List Bool) (p : Option (Option Bool) × SignType)
    (rest : List Bool) (h : codeReadWork xs = some (p, rest)) :
    xs = (optOptBoolBits p.1 ++ signBits p.2) ++ rest := by
  simp only [codeReadWork, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨wr, r₁⟩, h₁, ⟨⟨wm, r₂⟩, h₂, h⟩⟩ := h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rw [codeReadWrite_sound xs wr r₁ h₁, codeReadSign_sound r₁ wm r₂ h₂]
  simp [List.append_assoc]

/-- A successful transition read consumes exactly the serialization of its result. [AB09, §1.4] -/
lemma codeReadActionK_sound {k n : ℕ} (xs : List Bool) (a : Action k Bool (Fin (n + 1)))
    (rest : List Bool) (h : codeReadActionK k n xs = some (a, rest)) :
    xs = actionBitsK a ++ rest := by
  simp only [codeReadActionK, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨im, r₁⟩, h₁, ⟨⟨ws, r₂⟩, h₂, ⟨⟨out, r₃⟩, h₃, ⟨⟨q, r₄⟩, h₄, h⟩⟩⟩⟩ := h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rw [codeReadSign_sound xs im r₁ h₁,
    codeReadVec_sound codeReadWork (fun p => optOptBoolBits p.1 ++ signBits p.2)
      codeReadWork_sound k r₁ ws r₂ h₂,
    codeReadOutput_sound r₂ out r₃ h₃, codeReadState_sound r₃ q r₄ h₄]
  simp [actionBitsK, List.append_assoc]

/-- Erasing the work-tape reader result gives the work-tape skipper. [AB09, §1.4] -/
lemma codeEraseWork (xs : List Bool) : (codeReadWork xs).map Prod.snd = codeSkipWork xs := by
  simp only [codeReadWork, codeSkipWork, bind, Option.map_bind, Function.comp_def, pure,
    Option.map_some]
  rw [← codeEraseWrite xs, ← codeErase_bind]
  congr 1; funext p
  simpa only [Option.map_eq_bind, Function.comp_def] using codeEraseSign p.2

/-- Erasing the transition reader result gives the transition skipper. [AB09, §1.4] -/
lemma codeEraseActionK (k n : ℕ) (xs : List Bool) :
    (codeReadActionK k n xs).map Prod.snd = codeSkipActionK k n xs := by
  have hv (ys : List Bool) :
      (codeReadVec codeReadWork k ys).map Prod.snd = codeSkipRepeat codeSkipWork k ys := by
    rw [codeEraseVec]
    exact congrArg (fun r => codeSkipRepeat r k ys) (funext codeEraseWork)
  simp only [codeReadActionK, codeSkipActionK, bind, Option.map_bind, Function.comp_def, pure,
    Option.map_some]
  rw [← codeEraseSign xs, ← codeErase_bind]
  congr 1; funext p
  rw [← hv p.2, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseOutput p.2, ← codeErase_bind]
  congr 1; funext p
  simpa only [Option.map_eq_bind, Function.comp_def] using codeEraseState (n + 1) p.2

/-- Every `k`-work-tape record has at least `4 * k + 5` bits. [AB09, §1.4]

**Proof sketch.** Each work tape contributes four bits. The input move and output contribute
four more, and the successor-state field contributes at least one. -/
lemma codeActionK_length {k n : ℕ} (a : Action k Bool (Fin (n + 1))) :
    4 * k + 5 ≤ (actionBitsK a).length := by
  have hs (s : SignType) : (signBits s).length = 2 := by cases s <;> rfl
  have ho (b : Option Bool) : (optBoolBits b).length = 2 := by
    rcases b with _ | b
    · rfl
    · cases b <;> rfl
  have hw (b : Option (Option Bool)) : (optOptBoolBits b).length = 2 := by
    rcases b with _ | (_ | b)
    · rfl
    · rfl
    · cases b <;> rfl
  have hq : 1 ≤ (optStateBits a.state).length := by
    cases a.state <;>
      simp only [optStateBits, unaryFin, List.length_cons, List.length_append,
        List.length_replicate, List.length_nil] <;> omega
  have hv : 4 * k ≤ ((List.finRange k).flatMap fun i =>
      optOptBoolBits (a.workTapes i).1 ++ signBits (a.workTapes i).2).length := by
    simpa using codeFlatMap_length (List.finRange k)
      (fun i => optOptBoolBits (a.workTapes i).1 ++ signBits (a.workTapes i).2) 4
      (fun i _ => by simp [hs, hw])
  simp only [actionBitsK, List.length_append, hs, ho]
  omega

/-- The work-symbol function reading `w₀` on tape `0` and `w₁` on tape `1`,
for the fixed table enumeration of `Turing.CodeNDTM.serialize`. -/
def workPair (w₀ w₁ : Option Bool) : Fin 2 → Option Bool :=
  fun j => if j = 0 then w₀ else w₁

/-- Serialization of one two-work-tape transition record: the input-head move,
then each work tape's optional write and move in tape order, then the emission
and the successor state — `Turing.actionBits` with a second work-tape record. -/
def actionBits₂ {n : ℕ} (a : Action 2 Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++
    optOptBoolBits (a.workTapes 0).1 ++ signBits (a.workTapes 0).2 ++
    optOptBoolBits (a.workTapes 1).1 ++ signBits (a.workTapes 1).2 ++
    optBoolBits a.output ++ optStateBits a.state

/-- The fixed one-work-tape serialization agrees with the generic record serialization. [AB09, §1.4] -/
lemma actionBits_eq_actionBitsK {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    actionBits a = actionBitsK a := by
  simp [actionBits, actionBitsK, List.finRange_succ, List.append_assoc]

/-- The fixed two-work-tape serialization agrees with the generic record serialization. [AB09, §1.4] -/
lemma actionBits₂_eq_actionBitsK {n : ℕ} (a : Action 2 Bool (Fin (n + 1))) :
    actionBits₂ a = actionBitsK a := by
  simp [actionBits₂, actionBitsK, List.finRange_succ, List.append_assoc]

/-- The fixed one-work-tape skipper agrees with the generic skipper at `k = 1`. [AB09, §1.4] -/
lemma codeSkipAction_eq_codeSkipActionK (n : ℕ) (xs : List Bool) :
    codeSkipAction n xs = codeSkipActionK 1 n xs := by
  have h1 (ys : List Bool) : codeSkipRepeat codeSkipWork 1 ys = codeSkipWork ys := by
    cases h : codeSkipWork ys <;> simp [codeSkipRepeat, h]
  simp only [codeSkipAction, codeSkipActionK, h1, codeSkipWork, bind, Option.bind_assoc]

/-! ## Table formats -/

/-- A machine-code format specifies a transition-table grammar under the shared
state-count and initial-state header, together with its parser laws and fallback. [AB09, §1.4] -/
structure CodeFormat where
  /-- the coded machines -/
  Code : Type
  /-- the transition table of a machine with `n + 1` states -/
  Table : ℕ → Type
  /-- one less than the number of states -/
  numStates : Code → ℕ
  /-- assemble a machine from its state count, initial state and table -/
  assemble : (n : ℕ) → Fin (n + 1) → Table n → Code
  /-- the format's fixed serialization -/
  serialize : Code → List Bool
  /-- the fixed serialization of a table -/
  tableBits : {n : ℕ} → Table n → List Bool
  /-- the table reader -/
  readTable : (n : ℕ) → List Bool → Option (Table n × List Bool)
  /-- the erased table reader -/
  skipTable : ℕ → List Bool → Option (List Bool)
  /-- the minimum number of table bits per state (the up-front guard constant) -/
  guard : ℕ
  /-- the machine denoted by every malformed string -/
  fallback : Code
  numStates_assemble : ∀ n q t, numStates (assemble n q t) = n
  serialize_assemble : ∀ n q (t : Table n),
    serialize (assemble n q t) = pairEncode n.bits (unaryFin q ++ tableBits t)
  assemble_surj : ∀ M, ∃ n q t, assemble n q t = M
  readTable_append : ∀ n (t : Table n) xs, readTable n (tableBits t ++ xs) = some (t, xs)
  readTable_sound : ∀ n xs (t : Table n) rest,
    readTable n xs = some (t, rest) → xs = tableBits t ++ rest
  readTable_erase : ∀ n xs, (readTable n xs).map Prod.snd = skipTable n xs
  tableBits_length : ∀ n (t : Table n), guard * (n + 1) ≤ (tableBits t).length

namespace CodeFormat

variable (F : CodeFormat)

/-- Parse a machine and retain its all-true padding; check the table-length guard
before reading any state-indexed table entries. [AB09, §1.4] -/
def parseFull (xs : List Bool) : Option (F.Code × List Bool) := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if F.guard * (n + 1) > rest.length then none else do
      let (q, rest) ← codeReadFin (n + 1) rest
      let (table, rest) ← F.readTable n rest
      if rest.all id then pure (F.assemble n q table, rest) else none

/-- Decode every string, choosing the format's fallback on any malformed input. [AB09, §1.4] -/
def decode (xs : List Bool) : F.Code := ((F.parseFull xs).map Prod.fst).getD F.fallback

/-- Check the same header, table-length guard and padding as the parser,
retaining only the unconsumed suffix. [AB09, §1.4] -/
def scan (xs : List Bool) : Option (List Bool) := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if F.guard * (n + 1) > rest.length then none else do
      let rest ← codeSkipFin (n + 1) rest
      let rest ← F.skipTable n rest
      if rest.all id then pure rest else none

/-- Return the consumed prefix when scanning succeeds and the fallback's serialization
when scanning fails. [AB09, §1.4] -/
def canonical (xs : List Bool) : List Bool :=
  (F.scan xs).casesOn (F.serialize F.fallback) fun tail => xs.take (xs.length - tail.length)

/-- Parsing a serialization followed by true padding recovers the machine and padding. [AB09, §1.4]

**Proof sketch.** The doubled header recovers the canonical state-count bits. The table-length
bound discharges the early guard; the initial-state and table inverse laws recover
the assembled machine and leave the replicated true suffix, which passes the padding test. -/
theorem parseFull_serialize_pad (M : F.Code) (m : ℕ) :
    F.parseFull (F.serialize M ++ List.replicate m true) =
      some (M, List.replicate m true) := by
  obtain ⟨n, q, t, rfl⟩ := F.assemble_surj M
  have hp (a b c : List Bool) : pairEncode a b ++ c = pairEncode a (b ++ c) := by
    simp [pairEncode, List.append_assoc]
  rw [F.serialize_assemble, hp]
  unfold parseFull
  rw [pairDecode_pairEncode]
  dsimp only [bind, Option.bind]
  rw [codeBitsNat_bits]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  have hlen := F.tableBits_length n t
  simp only [List.length_append, List.length_replicate] at *
  rw [if_neg (by omega)]
  simp only [List.append_assoc, codeReadFin_append, F.readTable_append,
    List.all_replicate, id_eq, ite_self, ↓reduceIte, pure]

/-- Decoding a serialization followed by arbitrary true padding recovers the machine. [AB09, §1.4] -/
theorem decode_serialize_pad (M : F.Code) (m : ℕ) :
    F.decode (F.serialize M ++ List.replicate m true) = M := by
  simp only [decode, parseFull_serialize_pad, Option.map_some, Option.getD_some]

/-- Every successful parse expresses the input as the decoded serialization and suffix. [AB09, §1.4]

**Proof sketch.** Decompose the successful parse and use the field and table soundness equations.
The canonical state-count check reconstructs the doubled header, giving exactly
the machine serialization followed by the retained suffix. -/
theorem parseFull_sound (xs : List Bool) (M : F.Code) (tail : List Bool)
    (h : F.parseFull xs = some (M, tail)) : xs = F.serialize M ++ tail := by
  unfold parseFull at h
  obtain ⟨⟨bits, rest⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · contradiction
  next hb =>
    have hb : bits = (codeBitsNat bits).bits := not_not.mp hb
    split at h
    · contradiction
    next _ =>
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨q, r₁⟩, hq, ⟨⟨table, r₂⟩, ht, h⟩⟩ := h
      split at h
      next hpad =>
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have htable := F.readTable_sound _ _ _ _ ht
        dsimp only at htable
        rw [F.serialize_assemble, eq_pairEncode_of_pairDecode xs bits rest hp,
          codeReadFin_sound rest q r₁ hq, htable]
        simp only [pairEncode, List.append_assoc]
        congr 1
        exact congrArg (List.flatMap fun b : Bool => [b, b]) hb
      · contradiction

/-- The erased scanner returns exactly the suffix retained by the full parser. [AB09, §1.4]

**Proof sketch.** Push suffix projection through the parser's binds and branches. The initial-state
and table erasure laws replace their readers by the corresponding skippers; the
header checks and final padding test are unchanged. -/
theorem scan_full (xs : List Bool) : F.scan xs = (F.parseFull xs).map Prod.snd := by
  simp only [scan, parseFull, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  dsimp only
  split <;> try simp only [Option.map_none]
  split <;> try simp only [Option.map_none, Option.map_bind, Function.comp_def]
  have h (q : Fin (codeBitsNat p.1 + 1) × List Bool) (t : F.Table (codeBitsNat p.1) × List Bool) :
      (if t.2.all id then some (F.assemble (codeBitsNat p.1) q.1 t.1, t.2) else none).map
          Prod.snd = (if t.2.all id then some t.2 else none) := by split <;> rfl
  simp only [pure, h]
  rw [← codeEraseFin _ _, ← codeErase_bind]
  congr 1; funext q
  rw [← F.readTable_erase, ← codeErase_bind]

/-- The scanner-based canonical prefix equals the serialization of the decoded machine. [AB09, §1.4] -/
theorem canonical_eq (xs : List Bool) : F.canonical xs = F.serialize (F.decode xs) := by
  unfold canonical decode
  rw [scan_full]
  cases h : F.parseFull xs with
  | none => rfl
  | some p =>
    rcases p with ⟨M, tail⟩
    simp only [Option.map_some, Option.getD_some]
    rw [F.parseFull_sound xs M tail h]
    simp

/-- The decoded serialization is no longer than the input or the fixed fallback,
whichever is longer. [AB09, §1.4] -/
theorem serialize_decode_length_le (α : List Bool) :
    (F.serialize (F.decode α)).length ≤ max α.length (F.serialize F.fallback).length := by
  rw [← F.canonical_eq]
  unfold canonical
  cases F.scan α with
  | none => exact Nat.le_max_right _ _
  | some tail => exact (List.length_take_le' _ _).trans (Nat.le_max_left _ _)

/-- The guarded table-size lower bound for the decoded machine is bounded by the
input length or the fallback length, whichever is larger. [AB09, §1.4] -/
theorem numStates_decode_le (α : List Bool) :
    F.guard * (F.numStates (F.decode α) + 1) ≤
      max α.length (F.serialize F.fallback).length := by
  have hsize := F.serialize_decode_length_le α
  obtain ⟨n, q, t, h⟩ := F.assemble_surj (F.decode α)
  rw [← h, F.serialize_assemble, length_pairEncode, List.length_append] at hsize
  rw [← h, F.numStates_assemble]
  have htable := F.tableBits_length n t
  omega

/-- A failed full parse decodes to the format's fallback. [AB09, §1.4] -/
theorem decode_of_parseFull_none (α : List Bool) (h : F.parseFull α = none) :
    F.decode α = F.fallback := by
  simp [decode, h]

/-- A failed table-length guard decodes to the fallback before table recursion. [AB09, §1.4] -/
theorem decode_of_guard_lt (α bits rest : List Bool) (hp : pairDecode α = some (bits, rest))
    (hg : rest.length < F.guard * (codeBitsNat bits + 1)) : F.decode α = F.fallback := by
  simp [decode, parseFull, hp, hg]

end CodeFormat

/-! ## Two-work-tape tables -/

/-- A two-work-tape transition table is indexed by state, input read, and both work reads. [AB09, §1.4] -/
abbrev CodeTable2 (n : ℕ) : Type :=
  Fin (n + 1) → Option Bool → Option Bool → Option Bool → Action 2 Bool (Fin (n + 1))

/-- Serialize all two-work-tape table entries in state, input, work-0, work-1 order. [AB09, §1.4] -/
def codeTable2Bits {n : ℕ} (t : CodeTable2 n) : List Bool :=
  (List.finRange (n + 1)).flatMap fun q =>
    ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
          actionBitsK (t q inp w₀ w₁)

/-- Read the 27 two-work-tape transition records for every state. [AB09, §1.4] -/
def codeReadTable2 (n : ℕ) : List Bool → Option (CodeTable2 n × List Bool) :=
  codeReadVec (codeReadSymbols (codeReadSymbols (codeReadSymbols (codeReadActionK 2 n)))) (n + 1)

/-- Skip the 27 two-work-tape transition records for every state. [AB09, §1.4] -/
def codeSkipTable2 (n : ℕ) : List Bool → Option (List Bool) :=
  codeSkipRepeat (codeSkipRepeat (codeSkipRepeat (codeSkipRepeat (codeSkipActionK 2 n) 3) 3) 3)
    (n + 1)

/-- Reading a serialized two-work-tape table recovers it and leaves the suffix untouched. [AB09, §1.4] -/
lemma codeReadTable2_append {n : ℕ} (t : CodeTable2 n) (xs : List Bool) :
    codeReadTable2 n (codeTable2Bits t ++ xs) = some (t, xs) :=
  codeReadVec_append _ _ (fun _ _ => codeReadSymbols_append _ _
    (fun _ _ => codeReadSymbols_append _ _
      (fun _ _ => codeReadSymbols_append _ _ codeReadActionK_append _ _) _ _) _ _) _ _ _

/-- A successful two-work-tape table read consumes exactly its serialization. [AB09, §1.4] -/
lemma codeReadTable2_sound {n : ℕ} (xs : List Bool) (t : CodeTable2 n) (rest : List Bool)
    (h : codeReadTable2 n xs = some (t, rest)) : xs = codeTable2Bits t ++ rest :=
  codeReadVec_sound _ _ (fun _ _ _ => codeReadSymbols_sound _ _
    (fun _ _ _ => codeReadSymbols_sound _ _
      (fun _ _ _ => codeReadSymbols_sound _ _ codeReadActionK_sound _ _ _) _ _ _) _ _ _)
    _ _ _ _ h

/-- Erasing the two-work-tape table reader result gives the corresponding skipper. [AB09, §1.4] -/
lemma codeEraseTable2 (n : ℕ) (xs : List Bool) :
    (codeReadTable2 n xs).map Prod.snd = codeSkipTable2 n xs := by
  have ht := codeEraseVec
    (codeReadSymbols (codeReadSymbols (codeReadSymbols (codeReadActionK 2 n)))) (n + 1) xs
  simp only [codeEraseSymbols, codeEraseActionK] at ht
  exact ht

/-- Every two-work-tape table has at least 351 bits per state. [AB09, §1.4]

**Proof sketch.** Every record has at least 13 bits. Sum this lower bound over each of the
three possible symbols on each of three reads, giving 27 records and 351 bits
per state; then sum over the state enumeration. -/
lemma codeTable2Bits_length {n : ℕ} (t : CodeTable2 n) :
    351 * (n + 1) ≤ (codeTable2Bits t).length := by
  have hr : ∀ a : Action 2 Bool (Fin (n + 1)), 13 ≤ (actionBitsK a).length :=
    fun a => by have := codeActionK_length a; omega
  have h := codeFlatMap_length (List.finRange (n + 1))
    (fun q => ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
          actionBitsK (t q inp w₀ w₁)) 351 (by
      intro q _
      have h := codeFlatMap_length ([none, some false, some true] : List (Option Bool))
        (fun inp => ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
            actionBitsK (t q inp w₀ w₁)) 117 (by
          intro inp _
          have h := codeFlatMap_length ([none, some false, some true] : List (Option Bool))
            (fun w₀ => ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
              actionBitsK (t q inp w₀ w₁)) 39 (by
                intro w₀ _
                simpa using codeFlatMap_length
                  ([none, some false, some true] : List (Option Bool))
                  (fun w₁ => actionBitsK (t q inp w₀ w₁)) 13 (fun _ _ => hr _))
          simpa using h)
      simpa using h)
  simpa [codeTable2Bits] using h

/-! ## One-work-tape instance -/

private lemma codeReadActionK_one_append {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) (xs : List Bool) :
    codeReadActionK 1 n (actionBits a ++ xs) = some (a, xs) := by
  rw [actionBits_eq_actionBitsK]; exact codeReadActionK_append a xs

private lemma codeReadActionK_one_sound {n : ℕ} (xs : List Bool) (a : Action 1 Bool (Fin (n + 1)))
    (rest : List Bool) (h : codeReadActionK 1 n xs = some (a, rest)) :
    xs = actionBits a ++ rest := by
  rw [actionBits_eq_actionBitsK]; exact codeReadActionK_sound xs a rest h

private lemma codeEraseActionK_one (n : ℕ) (xs : List Bool) :
    (codeReadActionK 1 n xs).map Prod.snd = codeSkipAction n xs := by
  rw [codeEraseActionK, codeSkipAction_eq_codeSkipActionK]

/-- The one-work-tape `CodeTM` format has nine records per state and guard 81. [AB09, §1.4]

**Proof sketch.** The frozen record serialization is the generic one at one work tape. Nested
vector and symbol-reader laws provide table inversion, soundness and erasure;
summing the nine-bit record bound over the nine records gives guard 81. -/
def oneTapeFormat : CodeFormat where
  Code := CodeTM
  Table := fun n => Fin (n + 1) → Option Bool → Option Bool → Action 1 Bool (Fin (n + 1))
  numStates := CodeTM.numStates
  assemble := fun n q t => ⟨n, ⟨q, fun s inp w => t s inp (w 0)⟩⟩
  serialize := CodeTM.serialize
  tableBits := fun {n} t => (List.finRange (n + 1)).flatMap fun q =>
    ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
        actionBits (t q inp w)
  readTable := fun n =>
    codeReadVec (codeReadSymbols (codeReadSymbols (codeReadActionK 1 n))) (n + 1)
  skipTable := fun n =>
    codeSkipRepeat (codeSkipRepeat (codeSkipRepeat (codeSkipAction n) 3) 3) (n + 1)
  guard := 81
  fallback := codeFallback
  numStates_assemble := fun _ _ _ => rfl
  serialize_assemble := fun _ _ _ => rfl
  assemble_surj := by
    rintro ⟨n, q, tr⟩
    refine ⟨n, q, fun s inp w => tr s inp (fun _ => w), ?_⟩
    show CodeTM.mk n ⟨q, fun s inp w => tr s inp (fun _ => w 0)⟩ = CodeTM.mk n ⟨q, tr⟩
    congr 1
    congr 1
    funext s inp w
    apply congrArg (tr s inp)
    funext i
    exact congrArg w (Subsingleton.elim _ _)
  readTable_append := fun _ _ _ =>
    codeReadVec_append _ _ (fun _ _ => codeReadSymbols_append _ _
      (fun _ _ => codeReadSymbols_append _ _ codeReadActionK_one_append _ _) _ _) _ _ _
  readTable_sound := fun _ _ _ _ h =>
    codeReadVec_sound _ _ (fun _ _ _ => codeReadSymbols_sound _ _
      (fun _ _ _ => codeReadSymbols_sound _ _ codeReadActionK_one_sound _ _ _) _ _ _)
      _ _ _ _ h
  readTable_erase := fun n xs => by
    have ht := codeEraseVec (codeReadSymbols (codeReadSymbols (codeReadActionK 1 n))) (n + 1) xs
    simp only [codeEraseSymbols, codeEraseActionK_one] at ht
    exact ht
  tableBits_length := fun n t => by
    have hr : ∀ a : Action 1 Bool (Fin (n + 1)), 9 ≤ (actionBits a).length := fun a => by
      rw [actionBits_eq_actionBitsK]; have := codeActionK_length a; omega
    have h := codeFlatMap_length (List.finRange (n + 1))
      (fun q => ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
          actionBits (t q inp w)) 81 (by
        intro q _
        have h := codeFlatMap_length ([none, some false, some true] : List (Option Bool))
          (fun inp => ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (t q inp w)) 27 (by
              intro inp _
              simpa using codeFlatMap_length
                ([none, some false, some true] : List (Option Bool))
                (fun w => actionBits (t q inp w)) 9 (fun _ _ => hr _))
        simpa using h)
    simpa using h

/-- Total decoding: every malformed string denotes the fixed fallback. -/
def codeDecode (xs : List Bool) : CodeTM :=
  oneTapeFormat.decode xs

/-- The total decoder satisfies the required exact padded round-trip law. -/
lemma codeDecode_serialize_pad (M : CodeTM) (m : ℕ) :
    codeDecode (M.serialize ++ List.replicate m true) = M :=
  oneTapeFormat.decode_serialize_pad M m

/-- The erased parser: accept exactly the strings the parser accepts, returning only the unconsumed all-true suffix. -/
def codeScan (xs : List Bool) : Option (List Bool) :=
  oneTapeFormat.scan xs

/-- The canonical serialization of the machine a string denotes: the consumed prefix on scanner success, the fallback machine's serialization otherwise. -/
def codeCanonical (xs : List Bool) : List Bool :=
  oneTapeFormat.canonical xs

/-- The suffix scanner computes exactly the fixed serialization of the decoded machine. -/
lemma codeCanonical_eq (xs : List Bool) : codeCanonical xs = (codeDecode xs).serialize :=
  oneTapeFormat.canonical_eq xs

end Turing
