/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Decryption
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FirstTagged
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Games.BitCodec
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
# Polynomial-time garbled-gate evaluation

A gate's argument list is represented by an encoded list of unary indices.
The current vertex keys and its row table are encoded word lists. Padded lookup
reproduces the default key at an unavailable vertex. The published first-index
host finds the first row that nested special decryption opens.

## Main definitions

* `YaoHybridProof.keyLookup`: padded lookup in an encoded vertex-key list.
* `YaoHybridProof.argKeysCode`: encoded keys of the gate's arguments.
* `YaoHybridProof.nestedRowTagged`: the row adapter for first-success search.
* `YaoHybridProof.untagDefault`: the default key on search failure.
* `YaoHybridProof.evalGateWord`: encoded garbled-gate evaluation.

## Main results

* `YaoHybridProof.evalGateWord_poly`: polynomial time on every input word.
* `YaoHybridProof.evalGateWord_encoded`: correctness for `evalGate (nestedSpecial …)`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and §6.2.3.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof

open Complexity Turing BoolCircuit TCSlib.Cryptography

/-- On `⟨⟨N, values⟩, index⟩`, read the `|index|`-th word from `values`
and pad or truncate it to `|N|` bits. -/
def keyLookup (z : List Bool) : List Bool :=
  EnsembleLemmas.padL (pairFstD (pairFstD z)).length
    (BinArith.getW (pairEncode (pairSndD z) (pairSndD (pairFstD z))))

/-- For every `z`, `keyLookup z` is the padded `getW` lookup at its unary index. -/
theorem keyLookup_eq (z : List Bool) :
    keyLookup z = EnsembleLemmas.padL (pairFstD (pairFstD z)).length
      (BinArith.getW (pairEncode (pairSndD z) (pairSndD (pairFstD z)))) := rfl

/-- Padded encoded-key lookup is polynomial-time on every word. -/
theorem keyLookup_poly : PolyTimeComputable keyLookup := by
  have hN := polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have hv := polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have hraw := BinArith.polyTimeComputable_getW.comp
    (polyTimeComputable_pairSndD.pairEncode hv)
  simpa only [keyLookup_eq, PolyExpr.eval_var, Function.comp_apply] using
    EnsembleLemmas.polyTimeComputable_padL .var hN hraw

/-- Lookup from the encoded vector list returns the encoding of its defaulted entry:
`keyLookup ⟨⟨N, encWords (vs.map ofFn)⟩, 1^a⟩ = ofFn (vs.getD a default)`.

**Proof sketch.** Read the list lookup through its public encoded-list contract.
For an available vertex, padding inverts `List.ofFn`. For an unavailable vertex,
the empty lookup pads to the all-false key, which is the default vector. -/
theorem keyLookup_encoded (N : List Bool) (vs : List (Fin N.length → Bool)) (a : ℕ) :
    keyLookup (pairEncode (pairEncode N (BinArith.encWords (vs.map List.ofFn)))
        (List.replicate a true)) = List.ofFn (vs.getD a default) := by
  rw [keyLookup_eq, pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode,
    pairSndD_pairEncode, BinArith.getW_pairEncode, List.length_replicate,
    ← EnsembleLemmas.ofFn_padFin_eq_padL]
  apply congrArg List.ofFn
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : vs[a]? with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    rw [Games.padFin_nil]
    funext i
    rw [Games.zeroBits_apply]
    rfl
  | some k => simp only [Option.map_some, Option.getD_some, padFin_ofFn]

/-- On `⟨N, ⟨values, args⟩⟩`, map padded key lookup over the unary argument indices. -/
def argKeysCode (z : List Bool) : List Bool :=
  BinArith.mapW keyLookup
    (pairEncode (pairEncode (pairFstD z) (pairFstD (pairSndD z)))
      (pairSndD (pairSndD z)))

/-- For every `z`, `argKeysCode z` is `mapW keyLookup` with the parameter and
encoded vertex values as retained context and the argument indices as the list. -/
theorem argKeysCode_eq (z : List Bool) :
    argKeysCode z = BinArith.mapW keyLookup
      (pairEncode (pairEncode (pairFstD z) (pairFstD (pairSndD z)))
        (pairSndD (pairSndD z))) := rfl

/-- The encoded argument-key map `argKeysCode` is polynomial-time on every word. -/
theorem argKeysCode_poly : PolyTimeComputable argKeysCode :=
  (BinArith.polyTimeComputable_mapW keyLookup_poly).comp
    ((polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
        (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- On encoded vertices and unary arguments, `argKeysCode` is the encoded list
of the defaulted vertex keys at those argument indices. -/
theorem argKeysCode_encoded (N : List Bool) (vs : List (Fin N.length → Bool))
    (args : List ℕ) :
    argKeysCode (pairEncode N (pairEncode (BinArith.encWords (vs.map List.ofFn))
        (BinArith.encWords (args.map fun a => List.replicate a true)))) =
      BinArith.encWords ((args.map fun a => vs.getD a default).map List.ofFn) := by
  simp only [argKeysCode_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    BinArith.mapW_pairEncode, BinArith.decWords_encWords, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  exact keyLookup_encoded N vs a

/-- Adapt `⟨⟨N, keys⟩, row⟩` to the nested-decryption input `⟨N, ⟨keys, row⟩⟩`. -/
def nestedRowTagged (E₁ E₂ : List Bool → List Bool) (z : List Bool) : List Bool :=
  nestedDecTagged E₁ E₂ (pairEncode (pairFstD (pairFstD z))
    (pairEncode (pairSndD (pairFstD z)) (pairSndD z)))

/-- For every `z`, `nestedRowTagged E₁ E₂ z` runs `nestedDecTagged` with
parameter `fst (fst z)`, keys `snd (fst z)` and row `snd z`. -/
theorem nestedRowTagged_eq (E₁ E₂ : List Bool → List Bool) (z : List Bool) :
    nestedRowTagged E₁ E₂ z =
      nestedDecTagged E₁ E₂ (pairEncode (pairFstD (pairFstD z))
        (pairEncode (pairSndD (pairFstD z)) (pairSndD z))) := rfl

/-- For polynomial-time evaluators, the nested row adapter is polynomial-time. -/
theorem nestedRowTagged_poly {E₁ E₂ : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (nestedRowTagged E₁ E₂) :=
  (nestedDecTagged_poly hE₁ hE₂).comp
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
      ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).pairEncode
        polyTimeComputable_pairSndD))

/-- On `⟨N, tagged⟩`, return `|N|` false bits when the tag is empty and
otherwise remove its first bit. -/
def untagDefault (z : List Bool) : List Bool :=
  if pairSndD z = [] then List.replicate (pairFstD z).length false
  else (pairSndD z).drop 1

/-- For every `z`, `untagDefault z` is the zero key on empty tag and the
payload `drop 1 (snd z)` otherwise. -/
theorem untagDefault_eq (z : List Bool) :
    untagDefault z = if pairSndD z = [] then List.replicate (pairFstD z).length false
      else (pairSndD z).drop 1 := rfl

/-- Removing the tag and supplying the default zero key is polynomial-time. -/
theorem untagDefault_poly : PolyTimeComputable untagDefault := by
  simpa only [untagDefault_eq, PolyExpr.eval_var, Function.comp_apply, decide_eq_true_eq] using
    polyTimeComputable_ite (polyTimeComputable_isNil.comp polyTimeComputable_pairSndD)
      (EnsembleLemmas.polyTimeComputable_zeros .var polyTimeComputable_pairFstD)
      (polyTimeComputable_tail.comp polyTimeComputable_pairSndD)

/-- Untagging the encoded optional key gives the encoding of `o.getD default`,
including `N.length = 0`. -/
theorem untagDefault_encoded (N : List Bool) (o : Option (Fin N.length → Bool)) :
    untagDefault (pairEncode N (match o with | none => [] | some k => true :: List.ofFn k)) =
      List.ofFn (o.getD default) := by
  cases o with
  | none =>
    rw [untagDefault_eq, pairFstD_pairEncode, pairSndD_pairEncode, if_pos rfl]
    change List.replicate N.length false = List.ofFn (fun _ : Fin N.length => false)
    rw [List.ofFn_const]
  | some k =>
    rw [untagDefault_eq, pairFstD_pairEncode, pairSndD_pairEncode,
      if_neg (List.cons_ne_nil true (List.ofFn k))]
    rfl

/-- On `⟨N, ⟨args, ⟨values, rows⟩⟩⟩`, look up the gate's argument keys, scan
its rows for the first successful nested special decryption, and return the
resulting key or the default zero key. [PS10, Protocol 162.6] -/
noncomputable def evalGateWord (E₁ E₂ : List Bool → List Bool) (z : List Bool) : List Bool :=
  let N := pairFstD z
  let args := pairFstD (pairSndD z)
  let values := pairFstD (pairSndD (pairSndD z))
  let rows := pairSndD (pairSndD (pairSndD z))
  let keys := argKeysCode (pairEncode N (pairEncode values args))
  untagDefault (pairEncode N
    (firstTagged (nestedRowTagged E₁ E₂) (pairEncode (pairEncode N keys) rows)))

/-- For every `z`, `evalGateWord E₁ E₂ z` reads its parameter, argument indices,
vertex keys and row table, computes `argKeysCode`, applies `firstTagged` with
the nested-decryption row adapter and removes the tag with `untagDefault`. -/
theorem evalGateWord_eq (E₁ E₂ : List Bool → List Bool) (z : List Bool) :
    evalGateWord E₁ E₂ z =
  let N := pairFstD z
  let args := pairFstD (pairSndD z)
  let values := pairFstD (pairSndD (pairSndD z))
  let rows := pairSndD (pairSndD (pairSndD z))
  let keys := argKeysCode (pairEncode N (pairEncode values args))
  untagDefault (pairEncode N
    (firstTagged (nestedRowTagged E₁ E₂) (pairEncode (pairEncode N keys) rows))) := rfl

/-- For polynomial-time evaluators `E₁` and `E₂`, `evalGateWord E₁ E₂`
is polynomial-time on every input word. [PS10, Protocol 162.6]

**Proof sketch.** Read the four fields by pair projections. The argument-key map,
nested-decryption adapter and first-index adapter are polynomial-time on raw
words. Pair their inputs and compose their contracts, finishing with the
default-key untagging adapter. -/
theorem evalGateWord_poly {E₁ E₂ : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (evalGateWord E₁ E₂) := by
  have hN := polyTimeComputable_pairFstD
  have hargs := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have htail := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hvalues := polyTimeComputable_pairFstD.comp htail
  have hrows := polyTimeComputable_pairSndD.comp htail
  have hkeys := argKeysCode_poly.comp (hN.pairEncode (hvalues.pairEncode hargs))
  have hsearch := (firstTagged_poly (nestedRowTagged_poly hE₁ hE₂)).comp
    ((hN.pairEncode hkeys).pairEncode hrows)
  simpa only [evalGateWord_eq, Function.comp_apply] using
    untagDefault_poly.comp (hN.pairEncode hsearch)

/-- For every gate, vertex-value list and row table, the encoded evaluator returns
`List.ofFn (evalGate (nestedSpecial E₁ E₂ |N|) T v g vs)` on the corresponding
unary-argument and word-list encodings. No well-formedness or ciphertext-validity
hypothesis is needed. [PS10, Protocol 162.6]

**Proof sketch.** The argument-key map gives exactly the defaulted keys read by
`evalGate`. The nested row adapter tags precisely the optional decryption result.
The first-success contract therefore tags the table's `findSome?` result.
Removing its tag supplies exactly the defaulted key in `evalGate`'s public equation. -/
theorem evalGateWord_encoded (E₁ E₂ : List Bool → List Bool) (N : List Bool)
    (T : ℕ → List (List Bool)) (v : ℕ) (g : DAGGate)
    (vs : List (Fin N.length → Bool)) :
    evalGateWord E₁ E₂ (pairEncode N
        (pairEncode (BinArith.encWords (g.args.map fun a => List.replicate a true))
          (pairEncode (BinArith.encWords (vs.map List.ofFn)) (BinArith.encWords (T v))))) =
      List.ofFn (evalGate (nestedSpecial E₁ E₂ N.length) T v g vs) := by
  rw [evalGateWord_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [argKeysCode_encoded]
  have hsearch := firstTagged_encoded (β := Fin N.length → Bool) (nestedRowTagged E₁ E₂)
    (pairEncode N (BinArith.encWords
      ((g.args.map fun a => vs.getD a default).map List.ofFn))) (T v)
    ((nestedSpecial E₁ E₂ N.length).dec (g.args.map fun a => vs.getD a default))
    (fun k : Fin N.length → Bool => List.ofFn k) (fun row => by
      rw [nestedRowTagged_eq]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode]
      have hh := nestedDecTagged_encoded E₁ E₂ N (g.args.map fun a => vs.getD a default) row
      cases hd : (nestedSpecial E₁ E₂ N.length).dec
          (g.args.map fun a => vs.getD a default) row with
      | none => simpa only [hd] using hh
      | some k => simpa only [hd] using hh)
  rw [hsearch, evalGate_eq]
  have hh := untagDefault_encoded N
    ((T v).findSome? ((nestedSpecial E₁ E₂ N.length).dec
      (g.args.map fun a => vs.getD a default)))
  cases hd : (T v).findSome? ((nestedSpecial E₁ E₂ N.length).dec
      (g.args.map fun a => vs.getD a default)) with
  | none => simpa only [hd] using hh
  | some k => simpa only [hd] using hh

/-- Append the encoded evaluated key to the input value list in
`⟨N, ⟨args, ⟨values, rows⟩⟩⟩`. -/
noncomputable def evalGateAppendWord (E₁ E₂ : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairFstD (pairSndD (pairSndD z)) ++ pairEncode (evalGateWord E₁ E₂ z) []

/-- For every `z`, `evalGateAppendWord E₁ E₂ z` appends the pair-encoded output
of `evalGateWord E₁ E₂ z` to `fst (snd (snd z))`. -/
theorem evalGateAppendWord_eq (E₁ E₂ : List Bool → List Bool) (z : List Bool) :
    evalGateAppendWord E₁ E₂ z =
      pairFstD (pairSndD (pairSndD z)) ++ pairEncode (evalGateWord E₁ E₂ z) [] := rfl

/-- For polynomial-time `E₁` and `E₂`, appending the evaluated key to the
encoded value list is polynomial-time. -/
theorem evalGateAppendWord_poly {E₁ E₂ : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (evalGateAppendWord E₁ E₂) :=
  (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)).append
    ((evalGateWord_poly hE₁ hE₂).pairEncode (polyTimeComputable_const []))

/-- On the encoded gate arguments, values and table, appending the evaluated key
produces the encoding of `vs ++ [evalGate (nestedSpecial …) T v g vs]`. -/
theorem evalGateAppendWord_encoded (E₁ E₂ : List Bool → List Bool) (N : List Bool)
    (T : ℕ → List (List Bool)) (v : ℕ) (g : DAGGate)
    (vs : List (Fin N.length → Bool)) :
    evalGateAppendWord E₁ E₂ (pairEncode N
        (pairEncode (BinArith.encWords (g.args.map fun a => List.replicate a true))
          (pairEncode (BinArith.encWords (vs.map List.ofFn)) (BinArith.encWords (T v))))) =
      BinArith.encWords ((vs ++ [evalGate (nestedSpecial E₁ E₂ N.length) T v g vs]).map
        List.ofFn) := by
  rw [evalGateAppendWord_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [evalGateWord_encoded, List.map_append, List.map_singleton,
    BinArith.encWords_append_singleton]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof
