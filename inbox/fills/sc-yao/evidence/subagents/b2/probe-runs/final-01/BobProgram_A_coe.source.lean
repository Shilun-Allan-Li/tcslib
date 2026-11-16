/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobInit
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobTables
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobIO
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GarbledRun
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
# The complete generic polynomial-time garbled-circuit evaluator

A uniform circuit-description generator, initial-key constructor, table selector and
output reader assemble into one polynomial-time output function. The common-input,
message and answer selectors are arbitrary polynomial-time word maps. Only the
length of the common-input selector matters; its bits need not form a unary word.
The initial keys, tables and decoding pairs enter through explicit interface equations.

## Main definitions

None. The theorem uses the library's `runWith`, `evalGate` and nested special encryption.

## Main results

* `BobProgram.output_poly`: the complete encoded output-comparison vector is polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 162.6 (the evaluating party's computation).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobProgram

open Complexity Turing BoolCircuit

/-- For a uniform circuit family with valid output vertices, polynomial-time evaluators
and arbitrary polynomial-time parameter/message/answer selectors, the output-comparison
vector after garbled evaluation is polynomial-time. Initial keys, row tables and decoding
pairs are supplied through the stated reader equations. No well-formed-message hypothesis
is imposed. [PS10, Protocol 162.6]

**Proof sketch.** Normalize the parameter to unary before calling the uniform generator.
The public description decoder supplies the gate records. The initial-key machine and
raw table selector satisfy the generic garbled-run contracts, so the encoded complete
vertex list is polynomial-time. Normalize the message's decoding-pair list and retain the
uniform description's output list. The public output reader computes the desired vector.
The output vertices are available because `runWith` adds one value per gate and the initial
list has the circuit's input count. -/
theorem output_poly (inA inB outLen : PolyExpr)
    (circ : ∀ n, DAGCircuit (inA.eval n + inB.eval n))
    (outs : ∀ n, Fin (outLen.eval n) → ℕ)
    (houts : ∀ n j, outs n j < (circ n).size)
    {gen E₁ E₂ N msg ans : List Bool → List Bool}
    (hgen : PolyTimeComputable gen)
    (hgen_eq : ∀ n, gen (List.replicate n true) =
      pairEncode (circ n).encode
        (BinArith.encWords (List.ofFn fun j => encodeNat (outs n j))))
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (hN : PolyTimeComputable N) (hmsg : PolyTimeComputable msg)
    (hans : PolyTimeComputable ans)
    (init : ∀ z, List (Fin (N z).length → Bool))
    (T : List Bool → ℕ → List (List Bool)) (pairs : List Bool → List (List Bool))
    (hinit : ∀ z, BinArith.encWords ((init z).map List.ofFn) =
      BobInit.initWords (pairEncode (List.replicate (N z).length true)
        (pairEncode (List.replicate (inA.eval (N z).length) true)
          (pairEncode (List.replicate (inB.eval (N z).length) true)
            (pairEncode (msg z) (ans z))))))
    (hinit_length : ∀ z, (init z).length = inA.eval (N z).length + inB.eval (N z).length)
    (hT : ∀ z v, T z v =
      if inA.eval (N z).length + inB.eval (N z).length ≤ v then
        BinArith.decWords ((BinArith.decWords (pairFstD (msg z))).getD
          (v - (inA.eval (N z).length + inB.eval (N z).length)) []) else [])
    (hpairs : ∀ z, pairs z = BinArith.decWords (pairSndD (pairSndD (msg z)))) :
    PolyTimeComputable fun z =>
      let vals := runWith
        (fun g vs => evalGate (nestedSpecial E₁ E₂ (N z).length) (T z) vs.length g vs)
        (circ (N z).length).gates (init z)
      List.ofFn fun j : Fin (outLen.eval (N z).length) =>
        if List.ofFn (vals.getD (outs (N z).length j) default) =
            pairFstD ((pairs z).getD j []) then false
        else decide (List.ofFn (vals.getD (outs (N z).length j) default) =
          pairSndD ((pairs z).getD j [])) := by
  -- Decode the uniform description without imposing any raw-input shape.
  have hNu := polyTimeComputable_unary.comp' hN
  have hdesc := hgen.comp' hNu
  have hgateRaw := polyTimeComputable_pairSndD.comp'
    (DescriptionDecoder.readCircuit_poly.comp' (polyTimeComputable_pairFstD.comp' hdesc))
  have hgs : PolyTimeComputable fun z =>
      BinArith.encWords ((circ (N z).length).gates.map DescriptionDecoder.gateRecord) :=
    hgateRaw.congr fun z => by
      rw [hgen_eq, pairFstD_pairEncode, DescriptionDecoder.readCircuit_encode,
        pairSndD_pairEncode]
  have houtsCode : PolyTimeComputable fun z =>
      BinArith.encWords (List.ofFn fun j => encodeNat (outs (N z).length j)) :=
    (polyTimeComputable_pairSndD.comp' hdesc).congr fun z => by
      rw [hgen_eq, pairSndD_pairEncode]
  have hA := (polyTimeComputable_unaryPoly inA).comp' hN
  have hB := (polyTimeComputable_unaryPoly inB).comp' hN
  have hiRaw := BobInit.initWords_poly.comp'
    (hNu.pairEncode (hA.pairEncode (hB.pairEncode (hmsg.pairEncode hans))))
  have hi : PolyTimeComputable fun z => BinArith.encWords ((init z).map List.ofFn) :=
    hiRaw.congr fun z => (hinit z).symm
  -- The current-table machine discharges the generic traversal's reconstruction premise.
  let m : List Bool → List Bool := fun z =>
    List.replicate (inA.eval (N z).length + inB.eval (N z).length) true
  have hm : PolyTimeComputable m := EncodingMachines.unaryAdd_poly hA hB
  have hargs : ∀ g, pairSndD (DescriptionDecoder.gateRecord g) =
      BinArith.encWords (g.args.map fun a => List.replicate a true) := fun g => by
    rw [DescriptionDecoder.gateRecord_eq, pairSndD_pairEncode]
  have ht : ∀ z g (vs : List (Fin (N z).length → Bool)),
      BobTables.tableSelector m msg (pairEncode z
        (pairEncode (DescriptionDecoder.gateRecord g) (BinArith.encWords (vs.map List.ofFn)))) =
          BinArith.encWords (T z vs.length) := by
    intro z g vs
    rw [BobTables.tableSelector_host]
    simp only [m, List.length_replicate]
    rw [hT]
  let vals := fun z => runWith
    (fun g vs => evalGate (nestedSpecial E₁ E₂ (N z).length) (T z) vs.length g vs)
    (circ (N z).length).gates (init z)
  have hv : PolyTimeComputable fun z => BinArith.encWords ((vals z).map List.ofFn) :=
    garbledRunWith_poly hE₁ hE₂ hN DescriptionDecoder.gateRecord
      (fun z => (circ (N z).length).gates) init T hgs hi
      (BobTables.tableSelector_poly hm hmsg) hargs ht
  -- The circuit-size reader proves that every requested output is present.
  have hrange : ∀ z j, outs (N z).length j < (vals z).length := by
    intro z j
    have h := houts (N z).length j
    rw [DAGCircuit.size_eq] at h
    simpa only [vals, length_runWith, hinit_length] using h
  have hp : PolyTimeComputable fun z => BinArith.encWords (pairs z) :=
    (polyTimeComputable_reencodeWords.comp'
      (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' hmsg))).congr
        fun z => congrArg BinArith.encWords (hpairs z).symm
  have hcontext := hNu.pairEncode (hv.pairEncode (hp.pairEncode houtsCode))
  have hout := ((BobIO.outputWord_poly outLen).comp' hcontext).congr fun z =>
    BobIO.outputWord_layout outLen (vals z) (pairs z) (outs (N z).length) (hrange z)
  simpa only [vals] using hout

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobProgram
