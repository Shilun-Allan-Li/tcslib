/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeObjects
import TCSlib.Complexity.ClassP.BinaryArith.Words

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The canonical encoded simulated garbling message

This lightweight semantic interface gives the shared endpoint used by the simulated garbler
and the gate hybrids. Its three components are the simulated tables, Alice's false input
keys, and output decoding pairs ordered by the prescribed result bits.

## Main definitions

* `FakeObjects.message`: the complete simulated first message.

## Main results

* `FakeObjects.message_eq`: its exact table/key/pair encoding.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (Bob's simulated garbling message).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects

open Complexity Turing BoolCircuit

/-- The simulated first message is the encoded table vector paired with Alice's encoded
false-key vector and the encoded output pairs ordered by the prescribed result bits.
[PS10, Theorem 163.7] -/
noncomputable def message {inputs width : ℕ} {ρ : Type}
    (M : MultiEnc (Fin width → Bool) (List Bool) ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (inA outLen : ℕ)
    (output : Fin outLen → ℕ) (result : Fin outLen → Bool) : List Bool :=
  pairEncode (BinArith.encWords (List.ofFn fun i => BinArith.encWords (table M C s i)))
    (pairEncode
      (BinArith.encWords (List.ofFn fun v : Fin inA => List.ofFn (keyAt C s v false)))
      (BinArith.encWords (List.ofFn fun j =>
        pairEncode (List.ofFn (decodePair C s (output j) (result j)).1)
          (List.ofFn (decodePair C s (output j) (result j)).2))))

/-- `message M C s inA outLen output result` is
`⟨encWords (ofFn (encWords ∘ table)), ⟨encWords (ofFn key0), encWords (ofFn decodePair)⟩⟩`,
where keys are encoded by `List.ofFn` and each decoding pair by `pairEncode`. -/
theorem message_eq {inputs width : ℕ} {ρ : Type}
    (M : MultiEnc (Fin width → Bool) (List Bool) ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (inA outLen : ℕ)
    (output : Fin outLen → ℕ) (result : Fin outLen → Bool) :
    message M C s inA outLen output result =
      pairEncode (BinArith.encWords (List.ofFn fun i => BinArith.encWords (table M C s i)))
        (pairEncode
          (BinArith.encWords (List.ofFn fun v : Fin inA => List.ofFn (keyAt C s v false)))
          (BinArith.encWords (List.ofFn fun j =>
            pairEncode (List.ofFn (decodePair C s (output j) (result j)).1)
              (List.ofFn (decodePair C s (output j) (result j)).2)))) := rfl

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects
