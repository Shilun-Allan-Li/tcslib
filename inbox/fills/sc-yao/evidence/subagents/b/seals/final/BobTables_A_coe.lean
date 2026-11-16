/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FirstTagged
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
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && true) ||
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
# A total row-table selector for the garbled-evaluation host

The host retains input `x` and the encoded current vertex values. The selectors
`m x` and `msg x` provide an input-vertex count in unary and an arbitrary message.
Counting the current values gives the current vertex. A guarded unary subtraction
selects its table, with word-list normalization before either public lookup.

## Main definitions

* `BobTables.tableSelector`: the raw-word table selector for the generic evaluation host.

## Main results

* `BobTables.tableSelector_poly`: polynomial time on every host word.
* `BobTables.tableSelector_host`: its exact equation on a canonical host state.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 (reading a garbled table).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobTables

open Complexity Turing

/-- At `⟨x, ⟨gateRecord, values⟩⟩`, count the vertex values. If their count `v`
is at least `|m x|`, select table `v - |m x|` from the message's first component
and normalize its rows; otherwise return the empty encoded list. -/
def tableSelector (m msg : List Bool → List Bool) (w : List Bool) : List Bool :=
  let x := pairFstD w
  let v := (BinArith.decWords (pairSndD (pairSndD w))).length
  if (m x).length ≤ v then
    BinArith.encWords (BinArith.decWords (BinArith.getW
      (pairEncode (List.replicate (v - (m x).length) true)
        (BinArith.encWords (BinArith.decWords (pairFstD (msg x)))))))
  else []

/-- For every `w`, `tableSelector m msg w` compares the input-count word's
length with the current decoded-value count and normalizes the selected row table. -/
theorem tableSelector_eq (m msg : List Bool → List Bool) (w : List Bool) :
    tableSelector m msg w =
      let x := pairFstD w
      let v := (BinArith.decWords (pairSndD (pairSndD w))).length
      if (m x).length ≤ v then
        BinArith.encWords (BinArith.decWords (BinArith.getW
          (pairEncode (List.replicate (v - (m x).length) true)
            (BinArith.encWords (BinArith.decWords (pairFstD (msg x)))))))
      else [] := rfl

/-- For polynomial-time selectors `m` and `msg`, `tableSelector m msg` is
polynomial-time on every input word, including malformed messages and states.

**Proof sketch.** Count the current encoded values and compute the unary input
count. The existing unary subtraction gives their index difference. Normalize
the message's table list, use public word lookup at this index, and normalize
the selected rows. A polynomial-time length comparison guards the lookup result. -/
theorem tableSelector_poly {m msg : List Bool → List Bool}
    (hm : PolyTimeComputable m) (hmsg : PolyTimeComputable msg) :
    PolyTimeComputable (tableSelector m msg) := by
  have hvraw := BinArith.polyTimeComputable_countW.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hv : PolyTimeComputable fun w =>
      List.replicate (BinArith.decWords (pairSndD (pairSndD w))).length true :=
    hvraw.congr (fun w => by simp only [Function.comp_apply, BinArith.countW_eq])
  have hmraw := hm.comp polyTimeComputable_pairFstD
  have hmlen := polyTimeComputable_unary.comp hmraw
  have hindex := EncodingMachines.unarySub_poly hv hmlen
  have htables := polyTimeComputable_reencodeWords.comp
    (polyTimeComputable_pairFstD.comp (hmsg.comp polyTimeComputable_pairFstD))
  have hrows := polyTimeComputable_reencodeWords.comp
    (BinArith.polyTimeComputable_getW.comp (hindex.pairEncode htables))
  have htest := polyTimeComputable_lenLe.comp (hv.pairEncode hmraw)
  have h := polyTimeComputable_ite htest hrows (polyTimeComputable_const [])
  convert h using 1
  funext w
  simp only [tableSelector_eq, Function.comp_apply, pairFstD_pairEncode,
    pairSndD_pairEncode, List.length_replicate, decide_eq_true_eq]

/-- On `⟨x, ⟨gate, encWords (vs.map code)⟩⟩`, the selector returns the
encoded rows of message table `|vs| - |m x|` when `|m x| ≤ |vs|`, and the
empty encoded row list otherwise. The gate-record payload is immaterial. -/
theorem tableSelector_host {α : Type} (m msg : List Bool → List Bool)
    (x gate : List Bool) (vs : List α) (code : α → List Bool) :
    tableSelector m msg (pairEncode x
        (pairEncode gate (BinArith.encWords (vs.map code)))) =
      BinArith.encWords (if (m x).length ≤ vs.length then
        BinArith.decWords ((BinArith.decWords (pairFstD (msg x))).getD
          (vs.length - (m x).length) []) else []) := by
  rw [tableSelector_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, BinArith.decWords_encWords,
    List.length_map, BinArith.getW_pairEncode, List.length_replicate]
  split_ifs <;> simp only [BinArith.encWords_nil]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobTables
