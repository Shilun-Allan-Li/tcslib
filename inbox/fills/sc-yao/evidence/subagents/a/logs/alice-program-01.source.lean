/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GarblingProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.WordLists

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time Alice messages from generic circuit and seed readers

The interface assembles the actual encoded garbled tables, the selected input keys, and
the output decoding pairs. Circuit families, raw selectors, description maps, and seed block
equations are parameters. No definition from `Yao.lean` is visible.

## Main definitions

None.

## Main results

* `AliceProgram.selectedKeys_poly`: encoded selected input keys are polynomial-time.
* `AliceProgram.outputPairs_poly`: encoded decoding pairs are polynomial-time.
* `AliceProgram.message_poly`: the complete first garbling message is polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 162.6 (the first message of Alice).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram

open Complexity Turing BoolCircuit TCSlib.Cryptography.EncodingMachines

/-- The encoded list of `keyAt C s v (xs.getD v false)` for `v < count` is polynomial-time
when the unary width/bound/count maps and raw input/coin words are polynomial-time,
`count ≤ inputs`, and the seed satisfies its addressed-key equation.
[PS10, Protocol 162.6], Alice's selected input keys.

**Proof sketch.** On an indexed retained input, the index length is the input vertex and
a polynomial-time bit read selects its input bit. The generic addressed-key contract
computes the corresponding key word. Encode this indexed word vector with the public
range assembler; input-vertex bounds allow the supplied key reader at every genuine index. -/
theorem selectedKeys_poly (width bound count inputs : List Bool → ℕ)
    (xs coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hxs : PolyTimeComputable xs) (hcoins : PolyTimeComputable coins)
    (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hcount_le : ∀ z, count z ≤ inputs z)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun v : Fin (count z) =>
      List.ofFn (keyAt (C z) (s z) v ((xs z).getD v false))) := by
  let entry := fun z v => List.ofFn fun t : Fin (width z) => (coins z).getD
    ((((xs z).getD v false).toNat * bound z + v) * width z + t) false
  have hw : PolyTimeComputable fun w => List.replicate (width (pairSndD w)) true :=
    hwidth.comp polyTimeComputable_pairSndD
  have hb : PolyTimeComputable fun w => List.replicate (bound (pairSndD w)) true :=
    hbound.comp polyTimeComputable_pairSndD
  have hbit : PolyTimeComputable fun w =>
      [(xs (pairSndD w)).getD (pairFstD w).length false] :=
    getBit_poly (hxs.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD)
  have he : PolyTimeComputable fun w => entry (pairSndD w) (pairFstD w).length :=
    CoinGarbling.keyWord_poly (hcoins.comp polyTimeComputable_pairSndD) hw hb
      (unaryLength_poly polyTimeComputable_pairFstD) hbit
      (key := fun w (t : Fin (width (pairSndD w))) => (coins (pairSndD w)).getD
        ((((xs (pairSndD w)).getD (pairFstD w).length false).toNat * bound (pairSndD w) +
          (pairFstD w).length) * width (pairSndD w) + t) false) (fun _ _ => rfl)
  refine WordLists.ofFnTable_poly _ entry hcount he ?_
  intro z v
  have hv : (v : ℕ) < (C z).size := by
    rw [DAGCircuit.size_eq]
    have := hcount_le z
    omega
  exact congrArg List.ofFn (hkey z v hv ((xs z).getD v false))
