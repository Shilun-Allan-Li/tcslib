/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AliceProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeObjects
import TCSlib.Cryptography.Asymptotic.OneWay
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
# Polynomial-time simulated garbling programs

The simulated garbler shares the real garbler's addressed key, nonce, row, and bounded table
machines. Its output-key bit is always false; output decoding pairs use the prescribed
result bits. All circuit families and seed equations remain parameters.

## Main definitions

None.

## Main results

* `FakeProgram.activeAnswers_word`, `activeAnswers_poly`: canonical flat active-key answers.
* `FakeProgram.inputKeys_poly`, `outputPairs_poly`: active input keys and swapped output pairs.
* `FakeProgram.tables_poly`, `message_poly`: the complete actual simulated garbling program.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (simulation for Bob).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram

open Complexity Turing BoolCircuit TCSlib.Cryptography.EncodingMachines

/-- The canonical simulated answer is the concatenation of the false-key blocks beginning
at vertex `first`: `ofFn (activeAnswers C s first count) = flatten (ofFn (ofFn ∘ key0))`.
This reuses the published generic tuple-block identity. [PS10, Theorem 163.7] -/
theorem activeAnswers_word {inputs width : ℕ} {ρ : Type} (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ) :
    List.ofFn (FakeObjects.activeAnswers C s first count) =
      (List.ofFn fun i : Fin count => List.ofFn (keyAt C s (first + i) false)).flatten := by
  have heq : FakeObjects.activeAnswers C s first count =
      (FunFamily.blocks count width).symm (fun i => keyAt C s (first + i) false) := by
    funext t
    rw [FakeObjects.activeAnswers_eq, FunFamily.blocks_symm_apply]
  rw [heq, FunFamily.ofFn_blocks_symm]

/-- The canonical flat false-key answer is polynomial-time from unary width, bound,
starting vertex and count maps, a polynomial-time coin word, a valid input range, and the
seed's addressed-key equation. [PS10, Theorem 163.7]

**Proof sketch.** On an indexed retained input, add the unary index to the starting vertex
and read its false-key window. The public data-dependent concatenation loop emits one such
block per requested vertex. The generic tuple-block identity identifies this concatenation
with the canonical finite answer; the valid-range bound justifies every seed key reader. -/
theorem activeAnswers_poly (width bound first count inputs : List Bool → ℕ)
    (coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hfirst : PolyTimeComputable fun z => List.replicate (first z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hcoins : PolyTimeComputable coins) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hrange : ∀ z, first z + count z ≤ inputs z)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z =>
      List.ofFn (FakeObjects.activeAnswers (C z) (s z) (first z) (count z)) := by
  let entry := fun z i => RowFromCoins.keyWord width bound (fun v => first v + i)
    (fun _ => false) coins z
  have hv := unaryAdd_poly (hfirst.comp polyTimeComputable_pairSndD)
    (unaryLength_poly polyTimeComputable_pairFstD)
  have he : PolyTimeComputable fun w => entry (pairSndD w) (pairFstD w).length := by
    refine (RowFromCoins.keyWord_poly (hcoins.comp polyTimeComputable_pairSndD)
      (hwidth.comp polyTimeComputable_pairSndD) (hbound.comp polyTimeComputable_pairSndD)
      hv (polyTimeComputable_const [false])).congr fun w => ?_
    simp only [entry, RowFromCoins.keyWord_eq, Function.comp_apply]
  refine (ColMachines.polyTimeComputable_flatMap_range he hcount).congr fun z => ?_
  rw [activeAnswers_word, List.flatMap_def]
  apply congrArg List.flatten
  symm
  apply ofFn_eq_map_range
  intro i
  dsimp only [entry]
  rw [RowFromCoins.keyWord_eq]
  apply congrArg List.ofFn
  apply hkey
  rw [DAGCircuit.size_eq]
  have := hrange z
  omega

/-- Swapping each encoded pair according to the corresponding bit of a polynomial-time
result word preserves polynomial time. The pair vector is supplied by a polynomial-time
canonical encoding, and its unary length is polynomial-time. [PS10, Theorem 163.7]

**Proof sketch.** At a unary index, read the pair from its canonical word vector and read
the corresponding result bit. A conditional either swaps the two public pair projections
or retains the original pair. The existing indexed word-vector assembler encodes all these
entries; canonical list lookup identifies each entry with the requested pair. -/
theorem swapPairs_poly (count : List Bool → ℕ) (pairs result : List Bool → List Bool)
    (value : ∀ z, Fin (count z) → List Bool × List Bool)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hpairs : PolyTimeComputable pairs) (hresult : PolyTimeComputable result)
    (hshape : ∀ z, pairs z = BinArith.encWords (List.ofFn fun j =>
      pairEncode (value z j).1 (value z j).2)) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun j =>
      if (result z).getD j false then pairEncode (value z j).2 (value z j).1
      else pairEncode (value z j).1 (value z j).2) := by
  let lookup := fun z i => BinArith.getW (pairEncode (List.replicate i true) (pairs z))
  let entry := fun z i => if (result z).getD i false then
    pairEncode (pairSndD (lookup z i)) (pairFstD (lookup z i)) else lookup z i
  have hl : PolyTimeComputable fun w => lookup (pairSndD w) (pairFstD w).length :=
    BinArith.polyTimeComputable_getW.comp
      ((polyTimeComputable_unary.comp polyTimeComputable_pairFstD).pairEncode
        (hpairs.comp polyTimeComputable_pairSndD))
  have hb : PolyTimeComputable fun w =>
      [(result (pairSndD w)).getD (pairFstD w).length false] :=
    getBit_poly (hresult.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD)
  have he : PolyTimeComputable fun w => entry (pairSndD w) (pairFstD w).length :=
    polyTimeComputable_ite hb
      ((polyTimeComputable_pairSndD.comp hl).pairEncode
        (polyTimeComputable_pairFstD.comp hl)) hl
  refine WordLists.ofFnTable_poly _ entry hcount he ?_
  intro z j
  have hlookup : lookup z j = pairEncode (value z j).1 (value z j).2 := by
    dsimp only [lookup]
    rw [hshape z, BinArith.getW_pairEncode, List.length_replicate]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt), List.getElem_ofFn]
  dsimp only [entry]
  rw [hlookup, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The encoded simulated decoding-pair vector is polynomial-time from the real output
pair readers and a polynomial-time prescribed result word. Each result bit swaps the
corresponding two keys. [PS10, Theorem 163.7] -/
theorem outputPairs_poly (width bound count inputs : List Bool → ℕ)
    (description coins result : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hdescription : PolyTimeComputable description) (hcoins : PolyTimeComputable coins)
    (hresult : PolyTimeComputable result) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (output : ∀ z, Fin (count z) → ℕ)
    (houtsWord : ∀ z, pairSndD (description z) =
      BinArith.encWords (List.ofFn fun j => encodeNat (output z j)))
    (houtput_lt : ∀ z j, output z j < (C z).size)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun j : Fin (count z) =>
      pairEncode (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
        ((result z).getD j false)).1)
        (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
          ((result z).getD j false)).2)) := by
  let value := fun z (j : Fin (count z)) =>
    (List.ofFn (keyAt (C z) (s z) (output z j) false),
      List.ofFn (keyAt (C z) (s z) (output z j) true))
  let pairs := fun z => BinArith.encWords (List.ofFn fun j =>
    pairEncode (value z j).1 (value z j).2)
  have hp : PolyTimeComputable pairs := AliceProgram.outputPairs_poly
    width bound count inputs description coins hwidth hbound hcount hdescription hcoins
    C s output houtsWord houtput_lt hkey
  refine (swapPairs_poly count pairs result value hcount hp hresult (fun _ => rfl)).congr
    fun z => ?_
  apply congrArg BinArith.encWords
  apply congrArg List.ofFn
  funext j
  cases hb : (result z).getD j false <;>
    simp [value, FakeObjects.decodePair_eq]

/-- The encoded simulated Alice input-key vector contains the false key at every input
vertex and is polynomial-time under the real selected-key reader hypotheses.
[PS10, Theorem 163.7] -/
theorem inputKeys_poly (width bound count inputs : List Bool → ℕ)
    (coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hcoins : PolyTimeComputable coins) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hcount_le : ∀ z, count z ≤ inputs z)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun v : Fin (count z) =>
      List.ofFn (keyAt (C z) (s z) v false)) := by
  simpa only [List.getD_nil] using AliceProgram.selectedKeys_poly width bound count inputs
    (fun _ => []) coins hwidth hbound hcount (polyTimeComputable_const []) hcoins
    C s hcount_le hkey

/-- The actual encoded simulated table vector is polynomial-time from the generic uniform
circuit-description map and the seed's key, nonce, and XOR-permutation readers. Every row
plaintext is its output vertex's false key. [PS10, Theorem 163.7]

**Proof sketch.** Decode the canonical circuit description to the public gate-record word.
At a unary index, select its argument-word list and invoke the real garbler's generic row
core with the constant false output bit. The existing guarded table adapter enumerates at
most four rows, and the indexed word-vector assembler traverses all gate records. To prove
correctness, transport the retained context through the generic pointwise table contract.
Canonical record lookup fixes the argument list. Its fan-in bound removes the guard and
normalizes the dependent assignment enumeration. The arbitrary-output-bit row theorem then
identifies every enumerated row with the new simulated semantic object. -/
theorem tables_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) (width bound inputs : List Bool → ℕ)
    (description outs coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hdescription : PolyTimeComputable description) (hcoins : PolyTimeComputable coins)
    (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hshape : ∀ z, description z = pairEncode (C z).encode (outs z))
    (hfan : ∀ z (i : Fin (C z).gates.length), ((C z).gates[i]).args.length ≤ 2)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ z (i : Fin (C z).gates.length) a t, (s z).2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * i + t) false)) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun i =>
      BinArith.encWords (FakeObjects.table (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i)) := by
  let gates := GarblingProgram.gatesWord description
  let record := fun w => BinArith.getW (pairEncode (pairFstD w) (gates (pairSndD w)))
  let args := fun w => pairSndD (record w)
  let row := fun l a => RowFromCoins.rowWordWith E₁ E₂
    (fun w => width (pairSndD w)) (fun w => bound (pairSndD w))
    (fun w => inputs (pairSndD w)) (fun w => (pairFstD w).length)
    args (fun w => coins (pairSndD w)) (fun _ => false) l a
  let entry := TablesFromCoins.tableWordWith args row
  let entryVal := fun z i => entry (pairEncode (List.replicate i true) z)
  have hgates : PolyTimeComputable gates := GarblingProgram.gatesWord_poly hdescription
  have hgs (z : List Bool) :
      gates z = BinArith.encWords ((C z).gates.map DescriptionDecoder.gateRecord) :=
    GarblingProgram.gatesWord_description description z (C z) (outs z) (hshape z)
  have hrecord := BinArith.polyTimeComputable_getW.comp
    (polyTimeComputable_pairFstD.pairEncode (hgates.comp polyTimeComputable_pairSndD))
  have hargs : PolyTimeComputable args := polyTimeComputable_pairSndD.comp hrecord
  have hentry : PolyTimeComputable entry := TablesFromCoins.tableWordWith_poly row hargs
    (fun l _ a => RowFromCoins.rowWordWith_poly hE₁ hE₂
      (hwidth.comp polyTimeComputable_pairSndD) (hbound.comp polyTimeComputable_pairSndD)
      (hinputs.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD) hargs
      (hcoins.comp polyTimeComputable_pairSndD) (polyTimeComputable_const [false]) l a)
  have hcount : PolyTimeComputable fun z => List.replicate (C z).gates.length true := by
    refine (BinArith.polyTimeComputable_countW.comp hgates).congr fun z => ?_
    rw [Function.comp_apply, BinArith.countW_eq, hgs z,
      BinArith.decWords_encWords, List.length_map]
  have he : PolyTimeComputable fun w => entryVal (pairSndD w) (pairFstD w).length :=
    hentry.comp ((polyTimeComputable_unary.comp polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_pairSndD)
  refine WordLists.ofFnTable_poly _ entryVal hcount he ?_
  intro z i
  symm
  let w := pairEncode (List.replicate i true) z
  let args' := fun v => pairSndD (BinArith.getW
    (pairEncode (List.replicate i true) (gates v)))
  let row' := fun l a => RowFromCoins.rowWordWith E₁ E₂ width bound inputs
    (fun _ => i) args' coins (fun _ => false) l a
  have ha : args w = args' z := by
    simp only [args, args', record, w, pairFstD_pairEncode, pairSndD_pairEncode]
  have hr : ∀ l a, row l a w = row' l a z := by
    intro l a
    dsimp only [row, row']
    conv_lhs => rw [RowFromCoins.rowWordWith_value]
    conv_rhs => rw [RowFromCoins.rowWordWith_value]
    simp only [args, args', record, w, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate]
  change TablesFromCoins.tableWordWith args row w = _
  rw [TablesFromCoins.tableWordWith_congr_at args args' row row' w z ha hr]
  have hrec : BinArith.getW (pairEncode (List.replicate i true) (gates z)) =
      DescriptionDecoder.gateRecord ((C z).gates[i]) := by
    rw [hgs z, BinArith.getW_pairEncode, List.length_replicate]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact i.isLt), List.getElem_map]
    rfl
  have hcanonical : args' z =
      BinArith.encWords (((C z).gates[i]).args.map fun v => List.replicate v true) := by
    dsimp only [args']
    rw [hrec, DescriptionDecoder.gateRecord_eq, pairSndD_pairEncode]
  rw [TablesFromCoins.tableWordWith_of_encoded args' row' z _ (hfan z i) hcanonical,
    FakeObjects.table_eq]
  apply congrArg BinArith.encWords
  apply List.map_congr_left
  intro a _
  dsimp only [row']
  rw [FakeObjects.row_eq]
  exact RowFromCoins.rowWordWith_enc E₁ E₂ width bound inputs (fun _ => i) args' coins
    (fun _ => false) z (C z) (s z) i a (hfan z i) rfl hcanonical
    (hkey z) (hr₀ z i) (hr₁ z i) (hperm z i)

/-- The complete simulated Alice message is polynomial-time: simulated tables with false
row plaintexts, Alice's false input keys, and output pairs swapped by the prescribed output
word. The assumptions are the generic uniform-description and seed block readers, valid
input/output ranges, and polynomial-time raw selectors. [PS10, Theorem 163.7]

**Proof sketch.** The generic simulated-table program computes all false-output-key tables.
The real selected-key contract at a constant false input gives Alice's active input keys.
The real output-pair contract followed by the indexed bit-controlled swap gives the simulated
decoding information. Two applications of the public pairing closure assemble the message. -/
theorem message_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) (width bound inputs inA outLen : List Bool → ℕ)
    (description result coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hinA : PolyTimeComputable fun z => List.replicate (inA z) true)
    (houtLen : PolyTimeComputable fun z => List.replicate (outLen z) true)
    (hdescription : PolyTimeComputable description) (hresult : PolyTimeComputable result)
    (hcoins : PolyTimeComputable coins) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (output : ∀ z, Fin (outLen z) → ℕ)
    (hshape : ∀ z, description z = pairEncode (C z).encode
      (BinArith.encWords (List.ofFn fun j => encodeNat (output z j))))
    (hinA_le : ∀ z, inA z ≤ inputs z)
    (houtput_lt : ∀ z j, output z j < (C z).size)
    (hfan : ∀ z (i : Fin (C z).gates.length), ((C z).gates[i]).args.length ≤ 2)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ z (i : Fin (C z).gates.length) a t, (s z).2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * i + t) false)) :
    PolyTimeComputable fun z => pairEncode
      (BinArith.encWords (List.ofFn fun i =>
        BinArith.encWords (FakeObjects.table (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i)))
      (pairEncode
        (BinArith.encWords (List.ofFn fun v : Fin (inA z) =>
          List.ofFn (keyAt (C z) (s z) v false)))
        (BinArith.encWords (List.ofFn fun j : Fin (outLen z) =>
          pairEncode
            (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
              ((result z).getD j false)).1)
            (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
              ((result z).getD j false)).2)))) := by
  have ht := tables_poly hE₁ hE₂ width bound inputs description
    (fun z => BinArith.encWords (List.ofFn fun j => encodeNat (output z j))) coins
    hwidth hbound hinputs hdescription hcoins C s hshape hfan hkey hr₀ hr₁ hperm
  have hk := inputKeys_poly width bound inA inputs coins hwidth hbound hinA hcoins
    C s hinA_le hkey
  have houtsWord (z : List Bool) : pairSndD (description z) =
      BinArith.encWords (List.ofFn fun j => encodeNat (output z j)) := by
    rw [hshape z, pairSndD_pairEncode]
  have hp := outputPairs_poly width bound outLen inputs description coins result
    hwidth hbound houtLen hdescription hcoins hresult C s output houtsWord houtput_lt hkey
  exact ht.pairEncode (hk.pairEncode hp)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram
