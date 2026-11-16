/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
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
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && true) ||
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
# First successful tagged row in polynomial time

This adapter uses the existing bounded first-index host. Each row is tested by a
polynomial-time word function returning `[]` on failure and a nonempty tagged
payload on success. The result is its first successful payload, or `[]`.

## Main definitions

* `YaoHybridProof.firstTagged`: first nonempty row result, using `EncodingMachines.firstIdx`.

## Main results

* `YaoHybridProof.polyTimeComputable_reencodeWords`: normalize a word-list encoding.
* `YaoHybridProof.firstTagged_poly`: polynomial time on arbitrary row encodings.
* `YaoHybridProof.firstTagged_encoded`: agreement with `List.findSome?`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 (first successful row decryption).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof

open Complexity Turing

/-- Re-encoding the word list read from any word is polynomial-time:
`w ↦ BinArith.encWords (BinArith.decWords w)`.
It is `mapW pairSndD` with empty retained context. -/
theorem polyTimeComputable_reencodeWords :
    PolyTimeComputable fun w => BinArith.encWords (BinArith.decWords w) := by
  have h := (BinArith.polyTimeComputable_mapW polyTimeComputable_pairSndD).comp
    ((polyTimeComputable_const []).pairEncode polyTimeComputable_id)
  convert h using 1
  funext w
  rw [Function.comp_apply, BinArith.mapW_pairEncode]
  simp only [pairSndD_pairEncode, id_eq, List.map_id']

/-- On `⟨q, rows⟩`, return the first nonempty `F ⟨q, row⟩` among
`BinArith.decWords rows`, or `[]` if every result is empty.
The index is selected by the published bounded first-index host.
[PS10, Protocol 162.6] -/
noncomputable def firstTagged (F : List Bool → List Bool) (z : List Bool) : List Bool :=
  let rows := BinArith.decWords (pairSndD z)
  let i := EncodingMachines.firstIdx
    (fun j => !decide (F (pairEncode (pairFstD z) (rows.getD j [])) = [])) rows.length
  if rows.length ≤ i then [] else F (pairEncode (pairFstD z) (rows.getD i []))

/-- For every `z`, `firstTagged F z` uses the first index accepted by
`j ↦ !decide (F ⟨fst z, (decWords (snd z)).getD j []⟩ = [])`,
and returns `[]` when that index exhausts the row count. -/
theorem firstTagged_eq (F : List Bool → List Bool) (z : List Bool) :
    firstTagged F z =
      let rows := BinArith.decWords (pairSndD z)
      let i := EncodingMachines.firstIdx
        (fun j => !decide (F (pairEncode (pairFstD z) (rows.getD j [])) = [])) rows.length
      if rows.length ≤ i then [] else F (pairEncode (pairFstD z) (rows.getD i [])) := rfl

/-- For polynomial-time `F`, `firstTagged F` is polynomial-time on every input word.
[PS10, Protocol 162.6]

**Proof sketch.** Normalize the row encoding so that the public list-lookup reader
applies even to malformed input words. The bounded first-index host tests whether
`F` on the selected row is nonempty, using the polynomial-time row count as its
bound. Read the selected row once more and apply `F`, with an empty result when
the index reaches the row count. This reuses the existing search host. -/
theorem firstTagged_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (firstTagged F) := by
  have hcanon := polyTimeComputable_reencodeWords.comp polyTimeComputable_pairSndD
  have hlookup : PolyTimeComputable fun w =>
      (BinArith.decWords (pairSndD (pairSndD w))).getD (pairFstD w).length [] := by
    have h := BinArith.polyTimeComputable_getW.comp
      (polyTimeComputable_pairFstD.pairEncode (hcanon.comp polyTimeComputable_pairSndD))
    convert h using 1
    funext w
    simp only [Function.comp_apply, BinArith.getW_pairEncode]
  have htest := polyTimeComputable_not (polyTimeComputable_isNil.comp
    (hF.comp ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).pairEncode
      hlookup)))
  have hcount : PolyTimeComputable fun z =>
      List.replicate (BinArith.decWords (pairSndD z)).length true := by
    exact (BinArith.polyTimeComputable_countW.comp polyTimeComputable_pairSndD).congr
      (fun z => by rw [Function.comp_apply, BinArith.countW_eq])
  have hindex := EncodingMachines.polyTimeComputable_firstIdx
    (p := fun z j => !decide (F (pairEncode (pairFstD z)
      ((BinArith.decWords (pairSndD z)).getD j [])) = [])) htest hcount
  have hchosen := BinArith.polyTimeComputable_getW.comp (hindex.pairEncode hcanon)
  have hresult := hF.comp (polyTimeComputable_pairFstD.pairEncode hchosen)
  have hlast := polyTimeComputable_lenLe.comp (hindex.pairEncode hcount)
  have h := polyTimeComputable_ite hlast (polyTimeComputable_const []) hresult
  convert h using 1
  funext z
  simp only [firstTagged_eq, Function.comp_apply, pairFstD_pairEncode,
    pairSndD_pairEncode, BinArith.getW_pairEncode, List.length_replicate, decide_eq_true_eq]

/-- If `F ⟨q, row⟩` tags `f row` by `none ↦ []`, `some b ↦ true :: payload b`,
then `firstTagged F ⟨q, encWords rows⟩` tags `rows.findSome? f` in the same way.

**Proof sketch.** If every row fails, the first-index characterization gives the
row count. Otherwise the published first-success characterization splits the
list into a failing prefix, the successful row and the remaining suffix. The
first-index characterization selects exactly the prefix length, whose lookup
is the successful row. -/
theorem firstTagged_encoded {β : Type} (F : List Bool → List Bool) (q : List Bool)
    (rows : List (List Bool)) (f : List Bool → Option β) (payload : β → List Bool)
    (hspec : ∀ row, F (pairEncode q row) =
      match f row with | none => [] | some b => true :: payload b) :
    firstTagged F (pairEncode q (BinArith.encWords rows)) =
      match rows.findSome? f with | none => [] | some b => true :: payload b := by
  rw [firstTagged_eq, pairFstD_pairEncode, pairSndD_pairEncode, BinArith.decWords_encWords]
  dsimp only
  cases hfind : rows.findSome? f with
  | none =>
    have hnone := List.findSome?_eq_none_iff.mp hfind
    have hidx : EncodingMachines.firstIdx
        (fun j => !decide (F (pairEncode q (rows.getD j [])) = [])) rows.length =
          rows.length := by
      apply EncodingMachines.firstIdx_eq_of_forall
      intro i hi
      rw [List.getD_eq_getElem _ [] hi, hspec, hnone _ (List.getElem_mem hi)]
      rfl
    rw [hidx, if_pos le_rfl]
  | some b =>
    obtain ⟨pre, row, post, rfl, hrow, hpre⟩ := List.findSome?_eq_some_iff.mp hfind
    have hAt : (pre ++ row :: post).getD pre.length [] = row := by
      rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
    have hidx : EncodingMachines.firstIdx
        (fun j => !decide (F (pairEncode q ((pre ++ row :: post).getD j [])) = []))
          (pre ++ row :: post).length = pre.length := by
      apply EncodingMachines.firstIdx_eq_of
      · simp only [List.length_append, List.length_cons]
        omega
      · rw [hAt, hspec, hrow]
        rfl
      · intro i hi
        rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ [] hi,
          hspec, hpre _ (List.getElem_mem hi)]
        rfl
    rw [hidx, if_neg (by simp only [List.length_append, List.length_cons]; omega),
      hAt, hspec, hrow]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof
