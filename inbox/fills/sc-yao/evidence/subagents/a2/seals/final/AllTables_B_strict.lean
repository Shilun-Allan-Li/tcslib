/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TablesFromCoins
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.WordLists
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
# Polynomial-time assembly of all garbled tables

The indexed adapter reads one gate record from an encoded circuit gate list and supplies
its kind/argument fields to the total row/table machine. The outer machine counts gates
and encodes the table word at each index. Both machines work on arbitrary raw words.

## Main definitions

* `AllTables.entryWord`: one table at the unary index of a retained input word.
* `AllTables.allTablesWord`: the encoded list of all table words.

## Main results

* `AllTables.entryWord_poly`, `allTablesWord_poly`: polynomial-time assembly.
* `AllTables.allTablesWord_garbledTables`: correctness from indexed table contracts.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 162.6 (transmission of the garbled circuit).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables

open Complexity Turing BoolCircuit TCSlib.Cryptography.EncodingMachines

/-- On `⟨1^i, z⟩`, read gate `i` from the supplied encoded gate list, then build its encoded
row table from the retained unary data and coin word. [PS10, Protocol 162.6] -/
noncomputable def entryWord (E₁ E₂ : List Bool → List Bool)
    (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
    (w : List Bool) : List Bool :=
  let record := fun v => BinArith.getW (pairEncode (pairFstD v) (gates (pairSndD v)))
  TablesFromCoins.tableWord E₁ E₂
    (fun v => width (pairSndD v)) (fun v => bound (pairSndD v))
    (fun v => inputs (pairSndD v)) (fun v => (pairFstD v).length)
    (fun v => pairFstD (record v)) (fun v => pairSndD (record v))
    (fun v => coins (pairSndD v)) w

/-- `entryWord ... w` applies the total table adapter to the selected gate record and
retained numeric/coin data of `pairSndD w`, with gate index `|pairFstD w|`. -/
theorem entryWord_eq (E₁ E₂ : List Bool → List Bool)
    (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
    (w : List Bool) :
    entryWord E₁ E₂ width bound inputs gates coins w =
      let record := fun v => BinArith.getW (pairEncode (pairFstD v) (gates (pairSndD v)))
      TablesFromCoins.tableWord E₁ E₂
        (fun v => width (pairSndD v)) (fun v => bound (pairSndD v))
        (fun v => inputs (pairSndD v)) (fun v => (pairFstD v).length)
        (fun v => pairFstD (record v)) (fun v => pairSndD (record v))
        (fun v => coins (pairSndD v)) w := rfl

/-- The indexed table adapter is polynomial-time when its evaluators, encoded gate list,
coin word, and unary numeric maps are polynomial-time. [PS10, Protocol 162.6] -/
theorem entryWord_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) {width bound inputs : List Bool → ℕ}
    {gates coins : List Bool → List Bool}
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hgates : PolyTimeComputable gates) (hcoins : PolyTimeComputable coins) :
    PolyTimeComputable (entryWord E₁ E₂ width bound inputs gates coins) := by
  have hw : PolyTimeComputable fun v => List.replicate (width (pairSndD v)) true :=
    hwidth.comp polyTimeComputable_pairSndD
  have hb : PolyTimeComputable fun v => List.replicate (bound (pairSndD v)) true :=
    hbound.comp polyTimeComputable_pairSndD
  have hi : PolyTimeComputable fun v => List.replicate (inputs (pairSndD v)) true :=
    hinputs.comp polyTimeComputable_pairSndD
  have hrecord := BinArith.polyTimeComputable_getW.comp
    (polyTimeComputable_pairFstD.pairEncode (hgates.comp polyTimeComputable_pairSndD))
  exact TablesFromCoins.tableWord_poly hE₁ hE₂ hw hb hi
    (unaryLength_poly polyTimeComputable_pairFstD)
    (polyTimeComputable_pairFstD.comp hrecord) (polyTimeComputable_pairSndD.comp hrecord)
    (hcoins.comp polyTimeComputable_pairSndD)

/-- The encoded table list contains the indexed table words for every decoded gate:
`encWords ((range |decWords (gates z)|).map (fun i => entryWord ... ⟨1^i, z⟩))`.
[PS10, Protocol 162.6] -/
noncomputable def allTablesWord (E₁ E₂ : List Bool → List Bool)
    (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
    (z : List Bool) : List Bool :=
  BinArith.encWords ((List.range (BinArith.decWords (gates z)).length).map fun i =>
    entryWord E₁ E₂ width bound inputs gates coins (pairEncode (List.replicate i true) z))

/-- `allTablesWord ... z` encodes every indexed table word of the decoded gate list. -/
theorem allTablesWord_eq (E₁ E₂ : List Bool → List Bool)
    (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
    (z : List Bool) :
    allTablesWord E₁ E₂ width bound inputs gates coins z =
      BinArith.encWords ((List.range (BinArith.decWords (gates z)).length).map fun i =>
        entryWord E₁ E₂ width bound inputs gates coins (pairEncode (List.replicate i true) z)) :=
  rfl

/-- The complete encoded table list is polynomial-time when its evaluators, encoded gate
list, coin word, and unary numeric maps are polynomial-time. [PS10, Protocol 162.6]

**Proof sketch.** Count the encoded gate records in unary. Normalize an indexed input's
counter to unary and apply the polynomial-time indexed table adapter. The public
data-dependent range-list assembler encodes these table words at every gate index. -/
theorem allTablesWord_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) {width bound inputs : List Bool → ℕ}
    {gates coins : List Bool → List Bool}
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hgates : PolyTimeComputable gates) (hcoins : PolyTimeComputable coins) :
    PolyTimeComputable (allTablesWord E₁ E₂ width bound inputs gates coins) := by
  have hcount : PolyTimeComputable fun z =>
      List.replicate (BinArith.decWords (gates z)).length true := by
    convert BinArith.polyTimeComputable_countW.comp hgates using 1
    funext z
    rw [Function.comp_apply, BinArith.countW_eq]
  have he := (entryWord_poly hE₁ hE₂ hwidth hbound hinputs hgates hcoins).comp
    ((polyTimeComputable_unary.comp polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_pairSndD)
  exact WordLists.rangeTable_poly
    (entry := fun z i => entryWord E₁ E₂ width bound inputs gates coins
      (pairEncode (List.replicate i true) z)) hcount he

/-- If the gate word encodes `C.gates` and each indexed adapter supplies its encoded garbled
table, the outer adapter is exactly `encWords (ofFn (fun i => encWords (garbledTable ... i)))`.
[PS10, Protocol 162.6] -/
theorem allTablesWord_garbledTables (E₁ E₂ : List Bool → List Bool)
    (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
    (gateCode : DAGGate → List Bool) (z : List Bool) (C : DAGCircuit (inputs z))
    (s : GarbleSeed C (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hgates : gates z = BinArith.encWords (C.gates.map gateCode))
    (hentry : ∀ i : Fin C.gates.length,
      entryWord E₁ E₂ width bound inputs gates coins (pairEncode (List.replicate i true) z) =
        BinArith.encWords (garbledTable (nestedSpecial E₁ E₂ (width z)) C s i)) :
    allTablesWord E₁ E₂ width bound inputs gates coins z =
      BinArith.encWords (List.ofFn fun i =>
        BinArith.encWords (garbledTable (nestedSpecial E₁ E₂ (width z)) C s i)) := by
  rw [allTablesWord_eq, hgates, BinArith.decWords_encWords, List.length_map]
  apply congrArg BinArith.encWords
  symm
  apply ofFn_eq_map_range
  intro i
  exact (hentry i).symm


/-- On a canonical indexed input `⟨1^i, z⟩`, the adapter equals the table machine on the
retained data with gate index fixed to `i` and the selected record's kind/argument fields.
This equation includes arbitrary malformed retained words.

**Proof sketch.** Normalize the argument count before comparing the dependent finite
assignment lists. Both branches then use the same enumeration. At each row, freeze the
supplied data maps to their current values; the public pair readers identify these values
with the retained context and unary index. -/
theorem entryWord_pair (E₁ E₂ : List Bool → List Bool)
    (width bound inputs : List Bool → ℕ) (gates coins : List Bool → List Bool)
    (i : ℕ) (z : List Bool) :
    entryWord E₁ E₂ width bound inputs gates coins (pairEncode (List.replicate i true) z) =
      TablesFromCoins.tableWord E₁ E₂ width bound inputs (fun _ => i)
        (fun v => pairFstD (BinArith.getW (pairEncode (List.replicate i true) (gates v))))
        (fun v => pairSndD (BinArith.getW (pairEncode (List.replicate i true) (gates v))))
        coins z := by
  let w := pairEncode (List.replicate i true) z
  let record := fun v => BinArith.getW (pairEncode (pairFstD v) (gates (pairSndD v)))
  let record' := fun v => BinArith.getW (pairEncode (List.replicate i true) (gates v))
  let count := (BinArith.decWords (pairSndD (record' z))).length
  let left (l : ℕ) := BinArith.encWords
    ((Finset.univ : Finset (Fin l → Bool)).toList.map fun a =>
      RowFromCoins.rowWord E₁ E₂ (fun v => width (pairSndD v))
        (fun v => bound (pairSndD v)) (fun v => inputs (pairSndD v))
        (fun v => (pairFstD v).length) (fun v => pairFstD (record v))
        (fun v => pairSndD (record v)) (fun v => coins (pairSndD v)) l a w)
  let right (l : ℕ) := BinArith.encWords
    ((Finset.univ : Finset (Fin l → Bool)).toList.map fun a =>
      RowFromCoins.rowWord E₁ E₂ width bound inputs (fun _ => i)
        (fun v => pairFstD (record' v)) (fun v => pairSndD (record' v)) coins l a z)
  have hrecord : record w = record' z := by
    simp only [record, record', w, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [entryWord_eq, TablesFromCoins.tableWord_eq, TablesFromCoins.tableWord_eq]
  change (if (BinArith.decWords (pairSndD (record w))).length ≤ 2 then
    left (min (BinArith.decWords (pairSndD (record w))).length 2) else []) =
      if count ≤ 2 then right (min count 2) else []
  -- Normalize the natural arity before opening its dependent finite enumeration.
  rw [hrecord]
  change (if count ≤ 2 then left (min count 2) else []) =
    if count ≤ 2 then right (min count 2) else []
  by_cases h : count ≤ 2
  · rw [if_pos h, if_pos h]
    dsimp only [left, right]
    apply congrArg BinArith.encWords
    apply List.map_congr_left
    intro a _
    -- Freeze row data first, so paired-field readers never enter a dependent domain.
    conv_lhs => rw [RowFromCoins.rowWord_value]
    conv_rhs => rw [RowFromCoins.rowWord_value]
    simp only [record, record', w, pairFstD_pairEncode, pairSndD_pairEncode,
      List.length_replicate]
  · rw [if_neg h, if_neg h]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.AllTables
