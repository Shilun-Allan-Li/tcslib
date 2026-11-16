/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedSeed
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedRows
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && false) ||
            (false && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fixed selected-key slice messages and table descriptors

The circuit, original seed, row enumeration, selected wire and plaintext-key family are
fixed before the challenge key or nonce vector is supplied. The padded occurrence list
chooses every slice and precomputed message. Unused padding encrypts a fixed zero word.
Reconstruction records retain unaffected rows and reference the selected rows' challenge slots.

## Main definitions

* `SelectedPlan.record`: one row's fixed or challenge-dependent reconstruction record.
* `SelectedPlan.slotOffset`, `slotLength`, `slotWord`, `slotMessage`: all padded slice inputs.
* `SelectedPlan.tables`: the original table/row order of reconstruction records.
* `SelectedPlan.advice`: their serialized word with fixed surrounding view fields.

## Main results

* Exact padded slice-message lengths and reader contracts.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (all ciphertexts under one selected inactive key).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party
  computation*, Journal of Cryptology 22(2), 2009, pp. 161–188.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan

open Complexity Turing BoolCircuit TCSlib.Cryptography

variable {m n : ℕ} (C : DAGCircuit m)
  (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
  (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (u : Fin C.size) (q : ℕ)

/-- A row with no selected label retains its precomputed ciphertext. A selected row uses
the challenge descriptor for its unique selected argument and occurrence rank. -/
noncomputable def record (E₁ E₂ : List Bool → List Bool)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool) : List Bool :=
  (GateOccurrences.selectedPosition C.gates[i.val] a u.val).elim
    (SliceReconstruction.fixedRecord ((nestedSpecial E₁ E₂ n).enc
      (argKeys C s i a) (o i a) (s.2.1 i a)))
    (fun p => SelectedRows.descriptor n (argKeys C s i a) (s.2.1 i a) p.val
      (SelectedSeed.slotIndex C rows s.2.2 u.val i a p))

/-- `record` is a fixed ciphertext for an unselected row and the selected-layer descriptor
at its occurrence rank for a selected row. -/
theorem record_eq (E₁ E₂ : List Bool → List Bool)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool) :
    record C rows s u E₁ E₂ o i a =
      (GateOccurrences.selectedPosition C.gates[i.val] a u.val).elim
        (SliceReconstruction.fixedRecord ((nestedSpecial E₁ E₂ n).enc
          (argKeys C s i a) (o i a) (s.2.1 i a)))
        (fun p => SelectedRows.descriptor n (argKeys C s i a) (s.2.1 i a) p.val
          (SelectedSeed.slotIndex C rows s.2.2 u.val i a p)) := rfl

/-- A challenge slot has the selected row's layer offset, or zero for unused padding. -/
noncomputable def slotOffset (j : Fin (q + 1)) : ℕ :=
  (GateOccurrences.padded q (GateOccurrences.occurrences C rows s.2.2 u.val) j).elim 0 fun t =>
    SelectedRows.offset n
      (argKeys C s t.1 (s.2.2 t.1 ((rows t.1).getD t.2.1 (fun _ => false)))) t.2.2

/-- `slotOffset` reads the selected row's layer offset, with padding offset zero. -/
theorem slotOffset_eq (j : Fin (q + 1)) :
    slotOffset C rows s u q j =
      (GateOccurrences.padded q (GateOccurrences.occurrences C rows s.2.2 u.val) j).elim 0
        (fun t => SelectedRows.offset n
          (argKeys C s t.1 (s.2.2 t.1 ((rows t.1).getD t.2.1 (fun _ => false)))) t.2.2) := rfl

/-- A challenge slot has its selected row's message length, or `n` for unused padding. -/
noncomputable def slotLength (j : Fin (q + 1)) : ℕ :=
  (GateOccurrences.padded q (GateOccurrences.occurrences C rows s.2.2 u.val) j).elim n fun t =>
    SelectedRows.length n
      (argKeys C s t.1 (s.2.2 t.1 ((rows t.1).getD t.2.1 (fun _ => false)))) t.2.2

/-- `slotLength` reads the selected row's message length, with padding length `n`. -/
theorem slotLength_eq (j : Fin (q + 1)) :
    slotLength C rows s u q j =
      (GateOccurrences.padded q (GateOccurrences.occurrences C rows s.2.2 u.val) j).elim n
        (fun t => SelectedRows.length n
          (argKeys C s t.1 (s.2.2 t.1 ((rows t.1).getD t.2.1 (fun _ => false)))) t.2.2) := rfl

/-- A challenge slot's precomputed plaintext word uses only fixed keys and nonce halves;
unused padding has the fixed `n`-bit zero word. -/
noncomputable def slotWord (E₁ : List Bool → List Bool)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (j : Fin (q + 1)) : List Bool :=
  (GateOccurrences.padded q (GateOccurrences.occurrences C rows s.2.2 u.val) j).elim
    (List.replicate n false) fun t =>
      let a := s.2.2 t.1 ((rows t.1).getD t.2.1 (fun _ => false))
      SelectedRows.word E₁ n (argKeys C s t.1 a) (o t.1 a) (s.2.1 t.1 a) t.2.2

/-- `slotWord` reads the selected row's precomputed message, with zero-word padding. -/
theorem slotWord_eq (E₁ : List Bool → List Bool)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (j : Fin (q + 1)) :
    slotWord C rows s u q E₁ o j =
      (GateOccurrences.padded q (GateOccurrences.occurrences C rows s.2.2 u.val) j).elim
        (List.replicate n false) (fun t =>
          let a := s.2.2 t.1 ((rows t.1).getD t.2.1 (fun _ => false))
          SelectedRows.word E₁ n (argKeys C s t.1 a) (o t.1 a) (s.2.1 t.1 a) t.2.2) := rfl

/-- The typed padded slot message is `padFin` of its precomputed word at its slot length. -/
noncomputable def slotMessage (E₁ : List Bool → List Bool)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (j : Fin (q + 1)) : Fin (slotLength C rows s u q j) → Bool :=
  padFin (slotLength C rows s u q j) (slotWord C rows s u q E₁ o j)

/-- `slotMessage` is the padded typed view of the slot's precomputed word. -/
theorem slotMessage_eq (E₁ : List Bool → List Bool)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (j : Fin (q + 1)) :
    slotMessage C rows s u q E₁ o j =
      padFin (slotLength C rows s u q j) (slotWord C rows s u q E₁ o j) := rfl

/-- The descriptor tables retain every gate and every enumerated row in its original order. -/
noncomputable def tables (E₁ E₂ : List Bool → List Bool)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool)) :
    List (List (List Bool)) :=
  List.ofFn fun i => (rows i).map fun a => record C rows s u E₁ E₂ o i (s.2.2 i a)

/-- `tables` is the `ofFn` list of each gate's enumerated, permuted row records. -/
theorem tables_eq (E₁ E₂ : List Bool → List Bool)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool)) :
    tables C rows s u E₁ E₂ o =
      List.ofFn (fun i => (rows i).map fun a => record C rows s u E₁ E₂ o i (s.2.2 i a)) := rfl

/-- Every slot word has exactly its prescribed message length, including unused padding. -/
theorem slotWord_length
    {G₁ : ∀ k, (Fin k → Bool) → (Fin k → Bool) → (Fin (k + k) → Bool)}
    {E₁ : List Bool → List Bool}
    (hGE₁ : ∀ k (key nonce : Fin k → Bool),
      E₁ (pairEncode (List.ofFn key) (List.ofFn nonce)) = List.ofFn (G₁ k key nonce))
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (j : Fin (q + 1)) :
    (slotWord C rows s u q E₁ o j).length = slotLength C rows s u q j := by
  rw [slotWord_eq, slotLength_eq]
  cases hpad : GateOccurrences.padded q (GateOccurrences.occurrences C rows s.2.2 u.val) j with
  | none => simp only [Option.elim_none, List.length_replicate]
  | some t =>
    simp only [Option.elim_some]
    exact SelectedRows.word_length hGE₁ n _ _ _ _

/-- Encoding a typed slot message returns its precomputed word exactly, including padding. -/
theorem slotMessage_ofFn
    {G₁ : ∀ k, (Fin k → Bool) → (Fin k → Bool) → (Fin (k + k) → Bool)}
    {E₁ : List Bool → List Bool}
    (hGE₁ : ∀ k (key nonce : Fin k → Bool),
      E₁ (pairEncode (List.ofFn key) (List.ofFn nonce)) = List.ofFn (G₁ k key nonce))
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (j : Fin (q + 1)) :
    List.ofFn (slotMessage C rows s u q E₁ o j) = slotWord C rows s u q E₁ o j := by
  rw [slotMessage_eq, EnsembleLemmas.ofFn_padFin_eq_padL, EnsembleLemmas.padL_eq,
    ← slotWord_length C rows s u q hGE₁ o j, List.take_left]

/-- At a stored occurrence triple, all three slice readers are the corresponding row's
precomputed offset, message length and word after its fixed assignment permutation. -/
theorem slotReaders_of_padded (E₁ : List Bool → List Bool)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (j : Fin (q + 1)) (i : Fin C.gates.length) (row p : ℕ)
    (hpad : GateOccurrences.padded q (GateOccurrences.occurrences C rows s.2.2 u.val) j =
      some (i, row, p)) :
    let a := s.2.2 i ((rows i).getD row (fun _ => false))
    slotOffset C rows s u q j = SelectedRows.offset n (argKeys C s i a) p ∧
      slotLength C rows s u q j = SelectedRows.length n (argKeys C s i a) p ∧
      slotWord C rows s u q E₁ o j = SelectedRows.word E₁ n (argKeys C s i a)
        (o i a) (s.2.1 i a) p := by
  simp only [slotOffset_eq, slotLength_eq, slotWord_eq, hpad, Option.elim_some, and_self]

/-- Every padded slot's offset and message length fit in the joint pad of length
`2n+(n+(4n+2))`, including unused slots whose shape is `(0,n)`. -/
theorem slots_fit (j : Fin (q + 1)) :
    slotOffset C rows s u q j + n + slotLength C rows s u q j ≤
      (n + n) + (n + (4 * n + 2)) := by
  rw [slotOffset_eq, slotLength_eq]
  cases hpad : GateOccurrences.padded q (GateOccurrences.occurrences C rows s.2.2 u.val) j with
  | none =>
    simp only [Option.elim_none]
    exact (SelectedSlices.slice_shapes_fit n).1
  | some t =>
    simp only [Option.elim_some]
    exact SelectedRows.fits n _ _

/-- Two plaintext families give the same row record if they agree on rows with no selected
inactive argument. Selected-row records themselves do not contain the plaintext.

**Proof sketch.** For an unselected row, the fixed ciphertexts agree by the plaintext
hypothesis. For a selected row, both records are the same direct or known-key wrapped
challenge reference, independent of the plaintext family. -/
theorem record_congr (E₁ E₂ : List Bool → List Bool)
    (o₀ o₁ : (i : Fin C.gates.length) →
      (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (ho : GateOccurrences.selectedPosition C.gates[i.val] a u.val = none → o₀ i a = o₁ i a) :
    record C rows s u E₁ E₂ o₀ i a = record C rows s u E₁ E₂ o₁ i a := by
  rw [record_eq, record_eq]
  cases hsel : GateOccurrences.selectedPosition C.gates[i.val] a u.val with
  | none => simp only [Option.elim_none]; rw [ho hsel]
  | some p => simp only [Option.elim_some]

/-- Two plaintext families have the same complete descriptor tables when they agree on
all rows without a selected inactive argument. Thus both slice experiments use one advice. -/
theorem tables_congr (E₁ E₂ : List Bool → List Bool)
    (o₀ o₁ : (i : Fin C.gates.length) →
      (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (ho : ∀ i a, GateOccurrences.selectedPosition C.gates[i.val] a u.val = none →
      o₀ i a = o₁ i a) : tables C rows s u E₁ E₂ o₀ = tables C rows s u E₁ E₂ o₁ := by
  rw [tables_eq, tables_eq]
  apply congrArg List.ofFn
  funext i
  apply List.map_congr_left
  intro a _
  exact record_congr C rows s u E₁ E₂ o₀ o₁ i (s.2.2 i a) (ho i (s.2.2 i a))

/-- Fixed reconstruction advice serializes the descriptor tables, message tail, private input
and retained Alice output. No challenge key or nonce is an input to this construction. -/
noncomputable def advice (E₁ E₂ : List Bool → List Bool)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (tail privateInput aliceOutput : List Bool) : List Bool :=
  SliceReconstruction.advice
    (BinArith.encWords ((tables C rows s u E₁ E₂ o).map BinArith.encWords))
    tail privateInput aliceOutput

/-- `advice` is the reconstruction encoding of the descriptor tables and three fixed fields. -/
theorem advice_eq (E₁ E₂ : List Bool → List Bool)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (tail privateInput aliceOutput : List Bool) :
    advice C rows s u E₁ E₂ o tail privateInput aliceOutput =
      SliceReconstruction.advice
        (BinArith.encWords ((tables C rows s u E₁ E₂ o).map BinArith.encWords))
        tail privateInput aliceOutput := rfl

/-- Two plaintext families agreeing on every unselected row use the identical fixed advice,
when the surrounding fields are the same. -/
theorem advice_congr (E₁ E₂ : List Bool → List Bool)
    (o₀ o₁ : (i : Fin C.gates.length) →
      (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (ho : ∀ i a, GateOccurrences.selectedPosition C.gates[i.val] a u.val = none →
      o₀ i a = o₁ i a) (tail privateInput aliceOutput : List Bool) :
    advice C rows s u E₁ E₂ o₀ tail privateInput aliceOutput =
      advice C rows s u E₁ E₂ o₁ tail privateInput aliceOutput :=
  congrArg (fun ts : List (List (List Bool)) => SliceReconstruction.advice
    (BinArith.encWords (ts.map BinArith.encWords)) tail privateInput aliceOutput)
    (tables_congr C rows s u E₁ E₂ o₀ o₁ ho)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedPlan
