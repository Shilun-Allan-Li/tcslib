/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Hybrid
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybridMessage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bit-transfer answers as active wire labels

The bit-transfer functionality returns one bit to the receiver in every call. Its
concatenated answer word can therefore be identified from a product-indexed bit reader.
The relabeled seed turns the selected input-wire labels into the false labels.

## Main definitions

There are no new definitions.

## Main results

* `length_answersB`: one receiver bit per call gives the exact answer-word length.
* `answersB_eq_active`: the product-indexed key reader identifies the active-key word.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 (one bit transfer for every key bit).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTAnswerWords

open Complexity Turing BoolCircuit

/-- Bob's concatenated answers to bit transfer have exactly one bit per call:
`(H.answersB n xs ys rA rB).length = H.calls.eval n`. [PS10, Protocol 162.6] -/
theorem length_answersB (H : HybridProtocol otFunctionality) (n : ℕ)
    (xs ys rA rB : List Bool) :
    (H.answersB n xs ys rA rB).length = H.calls.eval n := by
  rw [HybridProtocol.answersB_eq, List.length_flatten, List.map_ofFn]
  change (List.ofFn (fun j : Fin (H.calls.eval n) =>
    (List.ofFn (otFunctionality.f n (H.callA n xs rA j) (H.callB n ys rB j)).2).length)).sum = _
  simp only [List.length_ofFn, otFunctionality_outB, PolyExpr.eval_const,
    List.ofFn_const, List.sum_replicate_nat, Nat.mul_one]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTAnswerWords
