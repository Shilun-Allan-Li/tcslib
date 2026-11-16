/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinRead
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FirstTagged
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
# Polynomial-time initial keys for a garbled evaluation

A context has shape `⟨N, ⟨A, ⟨B, ⟨message, answers⟩⟩⟩⟩`. The lengths of `N`, `A` and `B`
are the key width and the two input counts. At a position below `|A|`, the reader pads the
corresponding key of the message. At a later position it reads the corresponding key-width
block of the answer string. Every raw context and every index have a total interpretation.

## Main definitions

* `initEntry`: one initial key, selected by a unary index.
* `initWords`: the encoded list of the `|A| + |B|` initial keys.

## Main results

* `initEntry_poly`, `initWords_poly`: both operations are polynomial-time on all inputs.
* `initEntry_layout`, `initWords_layout`: the exact contracts on the context layout.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 (the evaluating party's initial wire keys).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit

open Complexity Turing

/-- On `⟨1^v, ⟨N, ⟨A, ⟨B, ⟨message, answers⟩⟩⟩⟩⟩`, return the padded message key
at `v < |A|`, otherwise the `|N|`-bit answer block from `(v - |A|) |N|`. -/
def initEntry (z : List Bool) : List Bool :=
  let ctx := pairSndD z
  let N := pairFstD ctx
  let A := pairFstD (pairSndD ctx)
  let msg := pairFstD (pairSndD (pairSndD (pairSndD ctx)))
  let ans := pairSndD (pairSndD (pairSndD (pairSndD ctx)))
  if (pairFstD z).length < A.length then
    EnsembleLemmas.padL N.length
      (BinArith.getW (pairEncode (pairFstD z)
        (BinArith.encWords (BinArith.decWords (pairFstD (pairSndD msg))))))
  else List.ofFn fun t : Fin N.length =>
    ans.getD (((pairFstD z).length - A.length) * N.length + t) false

/-- The entry reader selects the padded message key below `|A|`, and an answer block
otherwise, through total pair and encoded-list readers. -/
theorem initEntry_eq (z : List Bool) :
    initEntry z =
      let ctx := pairSndD z
      let N := pairFstD ctx
      let A := pairFstD (pairSndD ctx)
      let msg := pairFstD (pairSndD (pairSndD (pairSndD ctx)))
      let ans := pairSndD (pairSndD (pairSndD (pairSndD ctx)))
      if (pairFstD z).length < A.length then
        EnsembleLemmas.padL N.length
          (BinArith.getW (pairEncode (pairFstD z)
            (BinArith.encWords (BinArith.decWords (pairFstD (pairSndD msg))))))
      else List.ofFn fun t : Fin N.length =>
        ans.getD (((pairFstD z).length - A.length) * N.length + t) false := rfl

/-- The initial encoded word list has `|A| + |B|` entries, entry `v` being
`initEntry ⟨1^v, context⟩`. [PS10, Protocol 162.6] -/
def initWords (z : List Bool) : List Bool :=
  BinArith.encWords
    ((List.range ((pairFstD (pairSndD z)).length +
      (pairFstD (pairSndD (pairSndD z))).length)).map fun v =>
        initEntry (pairEncode (List.replicate v true) z))

/-- The initial encoded word list is the encoding of the entry reader over the range
`0, …, |A| + |B| - 1`. -/
theorem initWords_eq (z : List Bool) :
    initWords z = BinArith.encWords
      ((List.range ((pairFstD (pairSndD z)).length +
        (pairFstD (pairSndD (pairSndD z))).length)).map fun v =>
          initEntry (pairEncode (List.replicate v true) z)) := rfl

/-- Reading one initial key is polynomial-time on every raw context and unary index:
`PolyTimeComputable initEntry`. [PS10, Protocol 162.6]

**Proof sketch.** Normalize the message's encoded key list, look up the selected word,
and pad it to the key width. The other branch is a padded coin window at the unary offset
`(v - |A|) |N|`. Unary subtraction, multiplication and the comparison `v < |A|` are
published polynomial-time operations. They assemble the two branches without assuming
that any input or message is well formed. -/
theorem initEntry_poly : PolyTimeComputable initEntry := by
  let ctx := pairSndD
  let N := fun z => pairFstD (ctx z)
  let A := fun z => pairFstD (pairSndD (ctx z))
  let msg := fun z => pairFstD (pairSndD (pairSndD (pairSndD (ctx z))))
  let ans := fun z => pairSndD (pairSndD (pairSndD (pairSndD (ctx z))))
  have hc : PolyTimeComputable ctx := polyTimeComputable_pairSndD
  have hN : PolyTimeComputable N := polyTimeComputable_pairFstD.comp' hc
  have hA : PolyTimeComputable A :=
    polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hc)
  have hm : PolyTimeComputable msg := polyTimeComputable_pairFstD.comp'
    (polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' hc)))
  have ha : PolyTimeComputable ans := polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairSndD.comp'
      (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' hc)))
  let raw := fun z => BinArith.getW (pairEncode (pairFstD z)
    (BinArith.encWords (BinArith.decWords (pairFstD (pairSndD (msg z))))))
  have hr : PolyTimeComputable raw := BinArith.polyTimeComputable_getW.comp'
    (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_reencodeWords.comp'
      (polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hm))))
  have hpad0 := EnsembleLemmas.polyTimeComputable_padL .var (u := N) (a := raw) hN hr
  have hpad : PolyTimeComputable fun z => EnsembleLemmas.padL (N z).length (raw z) :=
    hpad0.congr fun z => by simp only [PolyExpr.eval_var]
  have hi := EncodingMachines.unaryLength_poly polyTimeComputable_pairFstD
  have hcount := EncodingMachines.unaryLength_poly hA
  have hwidth := EncodingMachines.unaryLength_poly hN
  have hw := polyTimeComputable_window ha
    (EncodingMachines.unaryMul_poly (EncodingMachines.unarySub_poly hi hcount) hwidth) hwidth
  have ht := EncodingMachines.ltTest_poly hi hcount
  refine (polyTimeComputable_ite ht hpad hw).congr (g := initEntry) fun z => ?_
  simp only [initEntry_eq, ctx, N, A, msg, ans, raw, decide_eq_true_eq]

/-- Constructing the entire encoded initial-key list is polynomial-time on every raw
context: `PolyTimeComputable initWords`. [PS10, Protocol 162.6]

**Proof sketch.** The lengths of the two input-count words are polynomial-time unary
counts. Add them, then apply the shared ordered-list encoder to the polynomial-time
entry reader, supplying each index in unary. -/
theorem initWords_poly : PolyTimeComputable initWords := by
  have hA := polyTimeComputable_pairFstD.comp' polyTimeComputable_pairSndD
  have hB := polyTimeComputable_pairFstD.comp'
    (polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD)
  have hc := EncodingMachines.unaryAdd_poly
    (EncodingMachines.unaryLength_poly hA) (EncodingMachines.unaryLength_poly hB)
  have he := initEntry_poly.comp'
    ((polyTimeComputable_unary.comp' polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_pairSndD)
  exact (WordLists.rangeTable_poly
    (count := fun z => (pairFstD (pairSndD z)).length +
      (pairFstD (pairSndD (pairSndD z))).length)
    (entry := fun z v => initEntry (pairEncode (List.replicate v true) z)) hc he).congr
      (g := initWords) fun z => (initWords_eq z).symm

/-- On the stated context layout, entry `v` is the `v`-th padded key decoded from the
message below `|A|`, and the answer block from `(v - |A|) |N|` otherwise. -/
theorem initEntry_layout (N A B msg ans : List Bool) (v : ℕ) :
    initEntry (pairEncode (List.replicate v true)
        (pairEncode N (pairEncode A (pairEncode B (pairEncode msg ans))))) =
      if v < A.length then
        List.ofFn (padFin N.length
          ((BinArith.decWords (pairFstD (pairSndD msg))).getD v []))
      else List.ofFn fun t : Fin N.length =>
        ans.getD ((v - A.length) * N.length + t) false := by
  simp only [initEntry_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, BinArith.getW_pairEncode, Fin.coe_cast,
    ← EnsembleLemmas.ofFn_padFin_eq_padL]

/-- On the context layout, the initial word list is the encoded vector of `|A| + |B|`
keys: the first `|A|` are padded message keys, and the rest are answer blocks.

**Proof sketch.** Replace the unary range map by the equal finite vector using the public
range/vector identity. Then apply the entry reader's layout contract at every position. -/
theorem initWords_layout (N A B msg ans : List Bool) :
    initWords (pairEncode N (pairEncode A (pairEncode B (pairEncode msg ans)))) =
      BinArith.encWords (List.ofFn fun v : Fin (A.length + B.length) =>
        if (v : ℕ) < A.length then
          List.ofFn (padFin N.length
            ((BinArith.decWords (pairFstD (pairSndD msg))).getD v []))
        else List.ofFn fun t : Fin N.length =>
          ans.getD (((v : ℕ) - A.length) * N.length + t) false) := by
  rw [initWords_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  apply congrArg BinArith.encWords
  refine Eq.trans (ofFn_eq_map_range
    (fun v : Fin (A.length + B.length) => initEntry (pairEncode (List.replicate v true)
      (pairEncode N (pairEncode A (pairEncode B (pairEncode msg ans))))))
    (fun v => initEntry (pairEncode (List.replicate v true)
      (pairEncode N (pairEncode A (pairEncode B (pairEncode msg ans))))))
    (fun _ => rfl)).symm ?_
  apply congrArg List.ofFn
  funext v
  exact initEntry_layout N A B msg ans v

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobInit
