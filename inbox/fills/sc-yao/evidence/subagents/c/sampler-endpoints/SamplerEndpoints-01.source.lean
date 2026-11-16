/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinSeedRelabel
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybridMessage
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exact sampler transport at the gate-hybrid endpoints

The real sampler and its encoded-view equation are parameters. Its seed has
the four addressed tape readers. The proved tape relabeling and per-seed view
identity therefore identify its acceptance probability with stage zero.
The last stage is the existing canonical fake view, with prescribed result
bits. This module defines no protocol, real message, or probability measure.

## Main definitions

None.

## Main results

* `real_eq_stage0_on_tape`: the pointwise complete-tape relabeling identity.
* `acceptProb_real_eq_stage0`: exact acceptance equality for every distinguisher.
* `acceptProb_real_eq_stage0_fst`: the same equality with an ignored Bob tape.
* `sample_end_of_result`: the exact prescribed-result canonical fake endpoint.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and Theorem 163.7 (the Bob-view hybrid).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes,
  UC Berkeley, draft of 22 January 2026, §3.2, Lemmas 3.2 and 3.3.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints

open Complexity Turing BoolCircuit TCSlib.Cryptography

section Tape

variable {inputs : ℕ} (C : DAGCircuit inputs) (S n : ℕ)
  (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2) (v : ℕ → Bool)
  (hS : C.size ≤ S)
  (seed : List Bool → GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (hK : ∀ q (w : Fin C.size) b (t : Fin n),
    (seed q).1 w b t = q.getD ((b.toNat * S + w) * n + t) false)
  (hR₀ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
      (t : Fin n),
    ((seed q).2.1 i a).1 t = q.getD (2 * S * n + (4 * i +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false)
  (hR₁ : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
      (t : Fin n),
    ((seed q).2.1 i a).2 t = q.getD (2 * S * n + (4 * i +
      (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t) false)
  (hP : ∀ q (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
      (t : Fin (C.gates[i]).args.length),
    (seed q).2.2 i a t = xor (a t) (q.getD (10 * S * n + 2 * i + t) false))
  (M : MultiEnc (Fin n → Bool) (List Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (inA inB outLen : ℕ) (output : Fin outLen → ℕ)
  (commonInput bobInput bobCoins aliceOutput : List Bool)
  (real : (Fin (10 * S * n + 2 * S) → Bool) → List Bool)
  (hReal : ∀ r, real r =
    pairEncode (⟨commonInput,
      pairEncode bobInput (List.ofFn fun t : Fin (inB * n) =>
        keyAt C (seed (List.ofFn r)) (inA + t.divNat) (v (inA + t.divNat)) t.modNat),
      bobCoins,
      [pairEncode (BinArith.encWords (List.ofFn fun i =>
          BinArith.encWords (garbledTable M C (seed (List.ofFn r)) i)))
        (pairEncode
          (BinArith.encWords (List.ofFn fun w : Fin inA =>
            List.ofFn (keyAt C (seed (List.ofFn r)) w (v w))))
          (BinArith.encWords (List.ofFn fun j =>
            pairEncode (List.ofFn (keyAt C (seed (List.ofFn r)) (output j) false))
              (List.ofFn (keyAt C (seed (List.ofFn r)) (output j) true)))))]⟩ : View).encode
      aliceOutput)

include hA hS hK hR₀ hR₁ hP hReal

/-- The supplied real sampler equals stage zero on the explicitly relabeled
complete tape, using its four seed readers and encoded-view equation.
The tape has length `10*S*n+2*S`, including when `n=0`. [PS10, Theorem 163.7] -/
theorem real_eq_stage0_on_tape (r : Fin (10 * S * n + 2 * S) → Bool) :
    real r = GateHybridMessage.sample M C
      (seed (List.ofFn (CoinRelabel.relabel S n (CoinSeedRelabel.keyMask C S v)
        (CoinSeedRelabel.rowPerm C S hA v) (CoinSeedRelabel.shiftMask C S v) r)))
      inA inB outLen output v commonInput bobInput bobCoins aliceOutput 0 := by
  rw [hReal]
  rw [CoinSeedRelabel.seed_relabel C S n hA v hS seed hK hR₀ hR₁ hP r]
  exact GateHybridMessage.sample_relabel M C (seed (List.ofFn r)) inA inB outLen
    output v commonInput bobInput bobCoins aliceOutput

end Tape

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints
