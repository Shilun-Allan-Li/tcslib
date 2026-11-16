/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Cryptography.Foundations.BitLists
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
            (true && coe && projection)
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
# Polynomial-time encoded word vectors

These contracts assemble an encoded word list from a polynomial-time unary count and a
polynomial-time indexed entry map. They reuse the public data-dependent concatenation
loop; no additional loop construction is introduced.

## Main definitions

None.

## Main results

* `WordLists.rangeTable_poly`: encode entries indexed by a unary range.
* `WordLists.ofFnTable_poly`: encode a typed vector through a total indexed entry adapter.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 162.6 (lists of garbled tables and selected keys).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.WordLists

open Complexity Turing

/-- Encoding a data-dependent list of entries is polynomial-time:
`z ↦ encWords ((range (count z)).map (entry z))`, if the unary count and the entry map
on `⟨1^i, z⟩` are polynomial-time. [PS10, Protocol 162.6] -/
theorem rangeTable_poly {count : List Bool → ℕ} {entry : List Bool → ℕ → List Bool}
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hentry : PolyTimeComputable fun w => entry (pairSndD w) (pairFstD w).length) :
    PolyTimeComputable fun z =>
      BinArith.encWords ((List.range (count z)).map (entry z)) := by
  have h := ColMachines.polyTimeComputable_flatMap_range
    (E := fun z i => pairEncode (entry z i) [])
    (hentry.pairEncode (polyTimeComputable_const [])) hcount
  simpa only [BinArith.encWords_def, List.flatMap_map, Function.comp_apply] using h

/-- Encoding a typed vector is polynomial-time when a total indexed adapter agrees with
its entries: if `f z i = entry z i`, then `z ↦ encWords (List.ofFn (f z))` is polynomial-time
from the unary count and the entry adapter on `⟨1^i, z⟩`. [PS10, Protocol 162.6] -/
theorem ofFnTable_poly {count : List Bool → ℕ} (f : ∀ z, Fin (count z) → List Bool)
    (entry : List Bool → ℕ → List Bool)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hentry : PolyTimeComputable fun w => entry (pairSndD w) (pairFstD w).length)
    (hf : ∀ z i, f z i = entry z i) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn (f z)) := by
  refine (rangeTable_poly hcount hentry).congr fun z => ?_
  apply congrArg BinArith.encWords
  exact (ofFn_eq_map_range (f z) (entry z) (hf z)).symm

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.WordLists
