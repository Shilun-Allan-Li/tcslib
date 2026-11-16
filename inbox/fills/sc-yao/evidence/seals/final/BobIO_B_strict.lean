/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
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
# Reading the output of an encoded garbled evaluation

The output reader takes a context `⟨1^n, ⟨values, ⟨pairs, outputs⟩⟩⟩`. The value list and
pair list use `BinArith.encWords`; the output-vertex list uses that encoding on unary numbers
with their terminating `false` bit. Every raw input has a total interpretation. A missing key
is padded to `n` bits before it is compared with the decoding pair.

## Main definitions

* `outputBit`: decode one output vertex, given its unary position in the output list.
* `outputWord`: decode a polynomial number of output positions.

## Main results

* `outputBit_poly`: the one-bit output reader is polynomial-time on every word.
* `outputWord_poly`: a polynomial number of decoded output bits is polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 (reading the output of the garbled circuit).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO

open Complexity Turing

/-- On `⟨⟨u, ⟨values, ⟨pairs, outputs⟩⟩⟩, 1^j⟩`, read output vertex `outputs[j]`, pad its
key from `values` to `|u|` bits, and decode it against `pairs[j]`: first key gives `false`,
otherwise equality to the second key gives `true`. All projections and lookups are total. -/
def outputBit (z : List Bool) : Bool :=
  let ctx := pairFstD z
  let j := pairSndD z
  let vals := pairFstD (pairSndD ctx)
  let pairs := pairFstD (pairSndD (pairSndD ctx))
  let outs := pairSndD (pairSndD (pairSndD ctx))
  let v := BinArith.uHead (BinArith.getW (pairEncode j outs))
  let k := EnsembleLemmas.padL (pairFstD ctx).length (BinArith.getW (pairEncode v vals))
  let p := BinArith.getW (pairEncode j pairs)
  if k = pairFstD p then false else decide (k = pairSndD p)

/-- The bit reader is the comparison of the padded value at the selected output vertex
with the two components of the selected decoding pair. -/
theorem outputBit_eq (z : List Bool) :
    outputBit z =
      let ctx := pairFstD z
      let j := pairSndD z
      let vals := pairFstD (pairSndD ctx)
      let pairs := pairFstD (pairSndD (pairSndD ctx))
      let outs := pairSndD (pairSndD (pairSndD ctx))
      let v := BinArith.uHead (BinArith.getW (pairEncode j outs))
      let k := EnsembleLemmas.padL (pairFstD ctx).length (BinArith.getW (pairEncode v vals))
      let p := BinArith.getW (pairEncode j pairs)
      if k = pairFstD p then false else decide (k = pairSndD p) := rfl

/-- The output word at context `z` has `p(|fst z|)` bits; bit `j` is
`outputBit ⟨z, 1^j⟩`. [PS10, Protocol 162.6] -/
def outputWord (p : PolyExpr) (z : List Bool) : List Bool :=
  List.ofFn fun j : Fin (p.eval (pairFstD z).length) =>
    outputBit (pairEncode z (List.replicate j true))

/-- The output reader's word is the list of `outputBit ⟨z, 1^j⟩` for
`j < p(|fst z|)`. -/
theorem outputWord_eq (p : PolyExpr) (z : List Bool) :
    outputWord p z = List.ofFn fun j : Fin (p.eval (pairFstD z).length) =>
      outputBit (pairEncode z (List.replicate j true)) := rfl

/-- The one-bit output reader is polynomial-time on every raw word:
`PolyTimeComputable (fun z => [outputBit z])`.

**Proof sketch.** Use unary word-list lookup for the output vertex and the decoding pair.
The vertex's key is another word-list lookup, padded to the parameter length. Two word
comparisons implement the decoding rule. Each lookup and padding operation is total, so
malformed words require no separate machine. -/
theorem outputBit_poly : PolyTimeComputable fun z => [outputBit z] := by
  let ctx := pairFstD
  let vals := fun z => pairFstD (pairSndD (ctx z))
  let pairs := fun z => pairFstD (pairSndD (pairSndD (ctx z)))
  let outs := fun z => pairSndD (pairSndD (pairSndD (ctx z)))
  have hc : PolyTimeComputable ctx := polyTimeComputable_pairFstD
  have hv : PolyTimeComputable vals :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hc)
  have hp : PolyTimeComputable pairs :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hc))
  have ho : PolyTimeComputable outs :=
    polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hc))
  let vertex := fun z => BinArith.uHead (BinArith.getW (pairEncode (pairSndD z) (outs z)))
  have hvertex : PolyTimeComputable vertex := BinArith.polyTimeComputable_uHead.comp
    (BinArith.polyTimeComputable_getW.comp (polyTimeComputable_pairSndD.pairEncode ho))
  let key := fun z => EnsembleLemmas.padL (pairFstD (ctx z)).length
    (BinArith.getW (pairEncode (vertex z) (vals z)))
  have hk0 := EnsembleLemmas.polyTimeComputable_padL .var
    (u := fun z => pairFstD (ctx z))
    (a := fun z => BinArith.getW (pairEncode (vertex z) (vals z)))
    (polyTimeComputable_pairFstD.comp' hc)
    (BinArith.polyTimeComputable_getW.comp' (hvertex.pairEncode hv))
  have hk : PolyTimeComputable key := hk0.congr (g := key) fun z => by
    simp only [key, PolyExpr.eval_var]
  let pair := fun z => BinArith.getW (pairEncode (pairSndD z) (pairs z))
  have hpair : PolyTimeComputable pair :=
    BinArith.polyTimeComputable_getW.comp (polyTimeComputable_pairSndD.pairEncode hp)
  have heq0 : PolyTimeComputable fun z => [decide (key z = pairFstD (pair z))] :=
    (polyTimeComputable_pairEq.comp
      (hk.pairEncode (polyTimeComputable_pairFstD.comp hpair))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have heq1 : PolyTimeComputable fun z => [decide (key z = pairSndD (pair z))] :=
    (polyTimeComputable_pairEq.comp
      (hk.pairEncode (polyTimeComputable_pairSndD.comp hpair))).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  refine (polyTimeComputable_ite heq0 (polyTimeComputable_const [false]) heq1).congr
    (g := fun z => [outputBit z]) ?_
  intro z
  by_cases h : key z = pairFstD (pair z) <;>
    simp only [outputBit_eq, ctx, vals, pairs, outs, vertex, key, pair] at h ⊢ <;>
    simp only [h, decide_true, decide_false, Bool.false_eq_true,
      if_true, if_false]

/-- The decoded output word has exactly `p(|fst z|)` bits. -/
theorem length_outputWord (p : PolyExpr) (z : List Bool) :
    (outputWord p z).length = p.eval (pairFstD z).length := List.length_ofFn

/-- Reading position `j` of the output word gives `outputBit ⟨z, 1^j⟩` in range and
`false` otherwise. -/
theorem outputWord_getD (p : PolyExpr) (z : List Bool) (j : ℕ) :
    (outputWord p z).getD j false =
      if j < p.eval (pairFstD z).length then
        outputBit (pairEncode z (List.replicate j true)) else false := by
  rw [outputWord_eq, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> rfl

/-- Decoding `p(|fst z|)` output bits is polynomial-time on every context word:
`PolyTimeComputable (outputWord p)`.

**Proof sketch.** The length of the output is the unary polynomial evaluator at the
parameter word. The output bit at a unary index is the polynomial-time bit reader, guarded
by the test that the index is below this length. Apply the published construction of a word
from its polynomial-time length and indexed-bit function. -/
theorem outputWord_poly (p : PolyExpr) : PolyTimeComputable (outputWord p) := by
  have hn : PolyTimeComputable fun w =>
      List.replicate (p.eval (pairFstD (pairSndD w)).length) true :=
    (polyTimeComputable_unaryPoly p).comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have ht := EncodingMachines.ltTest_poly
    (EncodingMachines.unaryLength_poly polyTimeComputable_pairFstD) hn
  have hb : PolyTimeComputable fun w =>
      [outputBit (pairEncode (pairSndD w)
        (List.replicate (pairFstD w).length true))] :=
    outputBit_poly.comp (polyTimeComputable_pairSndD.pairEncode
      (polyTimeComputable_unary.comp polyTimeComputable_pairFstD))
  refine EncodingMachines.polyTimeComputable_of_getD (F := outputWord p) ?_ ?_
  · refine (polyTimeComputable_ite ht hb (polyTimeComputable_const [false])).congr ?_
    intro w
    by_cases h : (pairFstD w).length < p.eval (pairFstD (pairSndD w)).length <;>
      simp only [outputWord_getD, h, decide_true, decide_false,
        Bool.false_eq_true, if_true, if_false]
  · exact ((polyTimeComputable_unaryPoly p).comp polyTimeComputable_pairFstD).congr
      fun z => by simp only [Function.comp_apply, length_outputWord]

/-- On encoded `n`-bit values, decoding pairs and unary output vertices, the bit reader
compares the value at `outs j` with the `j`-th pair. The vertex must be in the value list.

**Proof sketch.** The public word-list lookup equations read the output vertex and the
pair. The vertex is encoded in unary, so its leading ones give its value. In-range lookup
in the encoded value list returns the list of the selected bit vector, and padding this
list leaves it unchanged. -/
theorem outputBit_layout {n k : ℕ} (vs : List (Fin n → Bool)) (ps : List (List Bool))
    (outs : Fin k → ℕ) (j : Fin k) (hv : outs j < vs.length) :
    outputBit (pairEncode
        (pairEncode (List.replicate n true) (pairEncode (BinArith.encWords (vs.map List.ofFn))
          (pairEncode (BinArith.encWords ps)
            (BinArith.encWords (List.ofFn fun i => BoolCircuit.encodeNat (outs i))))))
        (List.replicate j true)) =
      if List.ofFn (vs.getD (outs j) default) = pairFstD (ps.getD j []) then false
      else decide (List.ofFn (vs.getD (outs j) default) = pairSndD (ps.getD j [])) := by
  have ho : (List.ofFn fun i => BoolCircuit.encodeNat (outs i)).getD j [] =
      BoolCircuit.encodeNat (outs j) := by
    rw [List.getD_eq_getElem _ _ (by simpa using j.isLt), List.getElem_ofFn]
  have hk : (vs.map List.ofFn).getD (outs j) [] = List.ofFn (vs.getD (outs j) default) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map,
      List.getD_eq_getElem _ _ hv]
  have hu := BinArith.uHead_encodeNat (outs j) []
  rw [List.append_nil] at hu
  simp only [outputBit_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    BinArith.getW_pairEncode, List.length_replicate, ho, hu]
  rw [hk, ← EnsembleLemmas.ofFn_padFin_eq_padL, padFin_ofFn]

/-- On encoded `n`-bit values, decoding pairs and `p(n)` unary output vertices,
`outputWord p` is the vector of comparisons with the selected decoding pairs. Every
output vertex must be present in the value list. [PS10, Protocol 162.6] -/
theorem outputWord_layout (p : PolyExpr) {n : ℕ} (vs : List (Fin n → Bool))
    (ps : List (List Bool)) (outs : Fin (p.eval n) → ℕ)
    (hv : ∀ j, outs j < vs.length) :
    outputWord p
        (pairEncode (List.replicate n true) (pairEncode (BinArith.encWords (vs.map List.ofFn))
          (pairEncode (BinArith.encWords ps)
            (BinArith.encWords (List.ofFn fun j => BoolCircuit.encodeNat (outs j)))))) =
      List.ofFn fun j =>
        if List.ofFn (vs.getD (outs j) default) = pairFstD (ps.getD j []) then false
        else decide (List.ofFn (vs.getD (outs j) default) = pairSndD (ps.getD j [])) := by
  simp only [outputWord_eq, pairFstD_pairEncode, List.length_replicate, Fin.coe_cast]
  apply congrArg List.ofFn
  funext j
  exact outputBit_layout vs ps outs j (hv j)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobIO
