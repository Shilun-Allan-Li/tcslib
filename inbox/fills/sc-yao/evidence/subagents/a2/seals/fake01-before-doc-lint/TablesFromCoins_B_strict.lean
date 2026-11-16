/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RowFromCoins
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
# Polynomial-time garbled tables from coin words

The total table adapter reads an encoded argument list. It computes the table only for
arity at most two, using three arbitrary constant assignment enumerations; higher arities
return the empty word. Thus malformed descriptions cannot induce exponential enumeration.

## Main definitions

* `TablesFromCoins.tableWord`: the encoded row list of one raw gate description.

## Main results

* `TablesFromCoins.tableWord_poly`: polynomial time on every string.
* `TablesFromCoins.tableWord_garbledTable`: identification through a row-level contract.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 162.6 (at most four encrypted rows per gate).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins

open Complexity Turing BoolCircuit TCSlib.Cryptography.EncodingMachines

/-- Encode a supplied row family using the argument-word count capped at two; counts
larger than two return `[]`. The row family can select either real or simulated plaintexts. -/
noncomputable def tableWordWith (args : List Bool → List Bool)
    (row : ∀ l : ℕ, (Fin l → Bool) → List Bool → List Bool) (z : List Bool) : List Bool :=
  let count := (BinArith.decWords (args z)).length
  let arity := min count 2
  if count ≤ 2 then BinArith.encWords
    ((Finset.univ : Finset (Fin arity → Bool)).toList.map fun a => row arity a z)
  else []

/-- `tableWordWith args row z` is the encoded fixed-enumeration row list for `count ≤ 2`,
and is `[]` for larger decoded argument counts. -/
theorem tableWordWith_eq (args : List Bool → List Bool)
    (row : ∀ l : ℕ, (Fin l → Bool) → List Bool → List Bool) (z : List Bool) :
    tableWordWith args row z =
      let count := (BinArith.decWords (args z)).length
      let arity := min count 2
      if count ≤ 2 then BinArith.encWords
        ((Finset.univ : Finset (Fin arity → Bool)).toList.map fun a => row arity a z)
      else [] := rfl

/-- The encoded row list of the supplied raw gate data for arity at most two; other
arities return `[]`. The finite assignment list is a constant for each arity.
[PS10, Protocol 162.6] -/
noncomputable def tableWord (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
    (z : List Bool) : List Bool :=
  tableWordWith args (fun l a =>
    RowFromCoins.rowWord E₁ E₂ width bound inputs gate kind args coins l a) z

/-- `tableWord ... z` is the encoded constant-enumeration row list at `min count 2`
when the decoded argument count is at most two, and is `[]` otherwise. -/
theorem tableWord_eq (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
    (z : List Bool) :
    tableWord E₁ E₂ width bound inputs gate kind args coins z =
      let count := (BinArith.decWords (args z)).length
      let arity := min count 2
      if count ≤ 2 then BinArith.encWords
        ((Finset.univ : Finset (Fin arity → Bool)).toList.map fun a =>
          RowFromCoins.rowWord E₁ E₂ width bound inputs gate kind args coins arity a z)
      else [] := rfl

/-- The guarded table assembler is polynomial-time if its argument word and every
supplied row map for the three possible arities are polynomial-time.

**Proof sketch.** Count argument words in unary and cap the count at two. Assemble each
of the three constant enumeration lists from its polynomial-time row maps, using the
bounded-arity table contract. A polynomial-time unary comparison rejects larger raw counts. -/
theorem tableWordWith_poly {args : List Bool → List Bool}
    (row : ∀ l : ℕ, (Fin l → Bool) → List Bool → List Bool)
    (hargs : PolyTimeComputable args)
    (hrow : ∀ l, l ≤ 2 → ∀ a, PolyTimeComputable (row l a)) :
    PolyTimeComputable (tableWordWith args row) := by
  -- Counting uses the public encoded-word-list counter.
  have hcount : PolyTimeComputable fun z =>
      List.replicate (BinArith.decWords (args z)).length true := by
    convert BinArith.polyTimeComputable_countW.comp hargs using 1
    funext z
    rw [Function.comp_apply, BinArith.countW_eq]
  have hcap := unaryMin_poly hcount (unaryConst_poly 2)
  have htable := Garbling.smallArityTable_poly
    (fun z => min (BinArith.decWords (args z)).length 2)
    (fun l => (Finset.univ : Finset (Fin l → Bool)).toList) row
    (fun _ => Nat.min_le_right _ _)
    (eqTest_poly hcap (unaryConst_poly 0)) (eqTest_poly hcap (unaryConst_poly 1)) hrow
  -- The guard covers arbitrary malformed argument-list words.
  convert polyTimeComputable_ite (leTest_poly hcount (unaryConst_poly 2)) htable
    (polyTimeComputable_const []) using 1
  funext z
  simp only [tableWordWith_eq, decide_eq_true_eq]

/-- The total table adapter is polynomial-time if the evaluators, coin/kind/argument words,
and unary numeric maps are polynomial-time. [PS10, Protocol 162.6]

**Proof sketch.** Count the argument words with the public polynomial-time list counter.
Cap the enumeration arity at two, so the enumeration is one of three fixed finite lists.
Every row is computed by the polynomial-time raw row machine. The finite-list assembly
contract gives the encoded table; a unary length test returns the empty word when the
uncapped count is larger than two. This covers all malformed input strings. -/
theorem tableWord_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) {width bound inputs gate : List Bool → ℕ}
    {kind args coins : List Bool → List Bool}
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hgate : PolyTimeComputable fun z => List.replicate (gate z) true)
    (hkind : PolyTimeComputable kind) (hargs : PolyTimeComputable args)
    (hcoins : PolyTimeComputable coins) :
    PolyTimeComputable (tableWord E₁ E₂ width bound inputs gate kind args coins) := by
  exact tableWordWith_poly _ hargs (fun l _ a =>
    RowFromCoins.rowWord_poly hE₁ hE₂ hwidth hbound hinputs hgate hkind hargs hcoins l a)

/-- On an encoded unary argument list of length at most two, the guarded table adapter
is precisely the encoded fixed-enumeration row list at that genuine argument length.

**Proof sketch.** Canonical decoding determines the argument-word count. The fan-in bound
removes the malformed-word guard and makes the capped arity equal the genuine length.
Normalize that natural arity before opening the dependent finite assignment enumeration. -/
theorem tableWordWith_of_encoded (args : List Bool → List Bool)
    (row : ∀ l : ℕ, (Fin l → Bool) → List Bool → List Bool) (z : List Bool)
    (vertices : List ℕ) (hfan : vertices.length ≤ 2)
    (hargs : args z = BinArith.encWords (vertices.map fun v => List.replicate v true)) :
    tableWordWith args row z = BinArith.encWords
      ((Finset.univ : Finset (Fin vertices.length → Bool)).toList.map fun a =>
        row vertices.length a z) := by
  have hcount : (BinArith.decWords (args z)).length = vertices.length := by
    rw [hargs, BinArith.decWords_encWords, List.length_map]
  have hcap : min (BinArith.decWords (args z)).length 2 = vertices.length := by
    rw [hcount, min_eq_left hfan]
  let emit (l : ℕ) := BinArith.encWords
    ((Finset.univ : Finset (Fin l → Bool)).toList.map fun a => row l a z)
  rw [tableWordWith_eq]
  change (if (BinArith.decWords (args z)).length ≤ 2 then
    emit (min (BinArith.decWords (args z)).length 2) else []) = emit vertices.length
  rw [if_pos (by rw [hcount]; exact hfan), hcap]

/-- On a genuine argument-word list, if every raw row equals the corresponding garbled
row after the seed permutation, the table adapter equals the encoded garbled table.
[PS10, Protocol 162.6]

**Proof sketch.** Canonical decoding identifies the argument count, so the cap and guard
leave the genuine arity unchanged. The fixed enumeration is then exactly the public
garbled-table enumeration, and the supplied row identity agrees at every enumerated row. -/
theorem tableWord_garbledTable (E₁ E₂ : List Bool → List Bool)
    (width bound inputs gate : List Bool → ℕ) (kind args coins : List Bool → List Bool)
    (z : List Bool) (C : DAGCircuit (inputs z))
    (s : GarbleSeed C (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (i : Fin C.gates.length) (hfan : (C.gates[i]).args.length ≤ 2)
    (hargs : args z = BinArith.encWords ((C.gates[i]).args.map fun v => List.replicate v true))
    (hrow : ∀ a,
      RowFromCoins.rowWord E₁ E₂ width bound inputs gate kind args coins
          (C.gates[i]).args.length a z =
        garbledRow (nestedSpecial E₁ E₂ (width z)) C s i (s.2.2 i a)) :
    tableWord E₁ E₂ width bound inputs gate kind args coins z =
      BinArith.encWords (garbledTable (nestedSpecial E₁ E₂ (width z)) C s i) := by
  change tableWordWith args (fun l a =>
    RowFromCoins.rowWord E₁ E₂ width bound inputs gate kind args coins l a) z = _
  rw [tableWordWith_of_encoded args _ z (C.gates[i]).args hfan hargs, garbledTable_eq]
  apply congrArg BinArith.encWords
  apply List.map_congr_left
  intro a _
  exact hrow a


/-- Two guarded table adapters agree at their inputs when their argument words agree
and their supplied row maps agree pointwise at every arity and assignment. -/
theorem tableWordWith_congr_at (args args' : List Bool → List Bool)
    (row row' : ∀ l : ℕ, (Fin l → Bool) → List Bool → List Bool) (z z' : List Bool)
    (hargs : args z = args' z') (hrow : ∀ l a, row l a z = row' l a z') :
    tableWordWith args row z = tableWordWith args' row' z' := by
  let left (l : ℕ) := BinArith.encWords
    ((Finset.univ : Finset (Fin l → Bool)).toList.map fun a => row l a z)
  let right (l : ℕ) := BinArith.encWords
    ((Finset.univ : Finset (Fin l → Bool)).toList.map fun a => row' l a z')
  rw [tableWordWith_eq, tableWordWith_eq]
  change (if (BinArith.decWords (args z)).length ≤ 2 then
    left (min (BinArith.decWords (args z)).length 2) else []) =
      if (BinArith.decWords (args' z')).length ≤ 2 then
        right (min (BinArith.decWords (args' z')).length 2) else []
  rw [hargs]
  split_ifs
  · dsimp only [left, right]
    apply congrArg BinArith.encWords
    apply List.map_congr_left
    intro a _
    exact hrow _ a
  · rfl


end TCSlib.Cryptography.SecureComputation.YaoHybridProof.TablesFromCoins
