/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybrids
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeMessage
import TCSlib.Cryptography.ZeroKnowledge.Interaction
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
# Encoded endpoints of the garbled-gate hybrid

The hybrid message uses the shared generic stage tables, active false input
keys and output decoding pairs. Its last stage is exactly the canonical fake
message. The first stage is the original real payload after seed relabeling.
The view sampler keeps the prescribed Alice output outside Bob's encoded view.

## Main definitions

* `message`: the encoded stage table/key/pair payload.
* `sample`: Bob's view with active answers and a fixed prescribed Alice output.

## Main results

* `message_relabel`, `activeAnswers_relabel`: per-seed first-endpoint identities.
* `message_end`, `sample_end`: exact canonical fake-message/view endpoints.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and Theorem 163.7 (the Bob-view hybrid).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage

open Complexity Turing BoolCircuit TCSlib.Cryptography

variable {inputs width : ℕ} {ρ : Type}

/-- The hybrid's first message encodes its stage tables, Alice's false keys,
and decoding pairs ordered by the prescribed output-wire values.
[PS10, Theorem 163.7] -/
noncomputable def message (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage : ℕ) : List Bool :=
  pairEncode (BinArith.encWords (List.ofFn fun i =>
      BinArith.encWords (GateHybrids.tableWith M C s (GateHybrids.stageBit C v stage) i)))
    (pairEncode
      (BinArith.encWords (List.ofFn fun w : Fin inA => List.ofFn (keyAt C s w false)))
      (BinArith.encWords (List.ofFn fun j =>
        pairEncode (List.ofFn (FakeObjects.decodePair C s (output j) (v (output j))).1)
          (List.ofFn (FakeObjects.decodePair C s (output j) (v (output j))).2))))

/-- `message ... stage` is the encoded stage-table vector paired with the
false-key vector and output-value-ordered decoding-pair vector. -/
theorem message_eq (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) (stage : ℕ) :
    message M C s inA outLen output v stage =
      pairEncode (BinArith.encWords (List.ofFn fun i =>
          BinArith.encWords (GateHybrids.tableWith M C s
            (GateHybrids.stageBit C v stage) i)))
        (pairEncode
          (BinArith.encWords (List.ofFn fun w : Fin inA => List.ofFn (keyAt C s w false)))
          (BinArith.encWords (List.ofFn fun j =>
            pairEncode (List.ofFn (FakeObjects.decodePair C s (output j) (v (output j))).1)
              (List.ofFn (FakeObjects.decodePair C s (output j) (v (output j))).2)))) := rfl

/-- The stage sampler pairs Bob's encoded view with the prescribed Alice output.
Bob's private input is his own word paired with the active false-key answers.
[PS10, Theorem 163.7] -/
noncomputable def sample (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool)
    (commonInput bobInput bobCoins aliceOutput : List Bool) (stage : ℕ) : List Bool :=
  pairEncode (⟨commonInput,
    pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C s inA inB)),
    bobCoins, [message M C s inA outLen output v stage]⟩ : View).encode aliceOutput

/-- `sample ... stage = pairEncode (view(commonInput,⟨bobInput,activeAnswers⟩,
bobCoins,[message stage]).encode) aliceOutput`. -/
theorem sample_eq (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool)
    (commonInput bobInput bobCoins aliceOutput : List Bool) (stage : ℕ) :
    sample M C s inA inB outLen output v commonInput bobInput bobCoins aliceOutput stage =
      pairEncode (⟨commonInput,
        pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C s inA inB)),
        bobCoins, [message M C s inA outLen output v stage]⟩ : View).encode aliceOutput := rfl

/-- False active answers under the relabeled seed are exactly the original
answers chosen by the wire values, including when the key width is zero. -/
theorem activeAnswers_relabel (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (v : ℕ → Bool) (first count : ℕ) :
    FakeObjects.activeAnswers C (RelabelGarbling.relabelSeed C v s) first count =
      fun t => keyAt C s (first + t.divNat) (v (first + t.divNat)) t.modNat := by
  funext t
  simp only [FakeObjects.activeAnswers_eq, RelabelGarbling.keyAt_relabel, Bool.false_xor]

/-- The output-value-ordered decoding pair under the relabeled seed is exactly
the original `(false key,true key)` pair, including default vertices. -/
theorem decodePair_relabel (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (v : ℕ → Bool) (w : ℕ) :
    FakeObjects.decodePair C (RelabelGarbling.relabelSeed C v s) w (v w) =
      (keyAt C s w false, keyAt C s w true) := by
  simp only [FakeObjects.decodePair_eq, RelabelGarbling.keyAt_relabel,
    Bool.xor_self, Bool.not_xor_self]

/-- The original real payload is exactly stage zero under the relabeled seed:
real tables, keys selected by input-wire values, and ordinary output pairs
become the stage tables, false keys, and output-value-ordered pairs.
[PS10, Theorem 163.7] -/
theorem message_relabel (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) :
    pairEncode (BinArith.encWords (List.ofFn fun i =>
        BinArith.encWords (garbledTable M C s i)))
      (pairEncode
        (BinArith.encWords (List.ofFn fun w : Fin inA =>
          List.ofFn (keyAt C s w (v w))))
        (BinArith.encWords (List.ofFn fun j =>
          pairEncode (List.ofFn (keyAt C s (output j) false))
            (List.ofFn (keyAt C s (output j) true))))) =
      message M C (RelabelGarbling.relabelSeed C v s) inA outLen output v 0 := by
  simp only [message_eq, ← GateHybrids.tableWith_start M C v s,
    RelabelGarbling.keyAt_relabel, Bool.false_xor, decodePair_relabel]

/-- The final-stage encoded payload is exactly the shared canonical fake
message, with result bits read at the output wires. [PS10, Theorem 163.7] -/
theorem message_end (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool) :
    message M C s inA outLen output v (2 * C.gates.length) =
      FakeObjects.message M C s inA outLen output (fun j => v (output j)) := by
  simp only [message_eq, FakeObjects.message_eq, GateHybrids.tableWith_end]

/-- The real payload and wire-value-selected OT answers give exactly the
stage-zero Bob-view sampler after seed relabeling. The prescribed Alice output
remains outside the encoded view. [PS10, Theorem 163.7] -/
theorem sample_relabel (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool)
    (commonInput bobInput bobCoins aliceOutput : List Bool) :
    pairEncode (⟨commonInput,
      pairEncode bobInput (List.ofFn fun t : Fin (inB * width) =>
        keyAt C s (inA + t.divNat) (v (inA + t.divNat)) t.modNat), bobCoins,
      [pairEncode (BinArith.encWords (List.ofFn fun i =>
          BinArith.encWords (garbledTable M C s i)))
        (pairEncode
          (BinArith.encWords (List.ofFn fun w : Fin inA =>
            List.ofFn (keyAt C s w (v w))))
          (BinArith.encWords (List.ofFn fun j =>
            pairEncode (List.ofFn (keyAt C s (output j) false))
              (List.ofFn (keyAt C s (output j) true)))))]⟩ : View).encode aliceOutput =
      sample M C (RelabelGarbling.relabelSeed C v s) inA inB outLen output v
        commonInput bobInput bobCoins aliceOutput 0 := by
  rw [sample_eq, activeAnswers_relabel, ← message_relabel]

/-- The last-stage view sampler is exactly Bob's canonical fake-message and
active-answer view, paired with the prescribed Alice output. [PS10, Theorem 163.7] -/
theorem sample_end (M : MultiEnc (Fin width → Bool) (List Bool) ρ)
    (C : DAGCircuit inputs) (s : GarbleSeed C (Fin width → Bool) ρ)
    (inA inB outLen : ℕ) (output : Fin outLen → ℕ) (v : ℕ → Bool)
    (commonInput bobInput bobCoins aliceOutput : List Bool) :
    sample M C s inA inB outLen output v commonInput bobInput bobCoins aliceOutput
        (2 * C.gates.length) =
      pairEncode (⟨commonInput,
        pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C s inA inB)),
        bobCoins, [FakeObjects.message M C s inA outLen output
          (fun j => v (output j))]⟩ : View).encode aliceOutput := by
  rw [sample_eq, message_end]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage
