/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.Normalization
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time bounded message-slot normalization

The message-slot normalization of [PS10, Theorem 175.1] is computed through the public generic
word-list map and lookup hosts, truncation, and the published counted emitter. No simulator
output-shape premise is used: malformed words are read by the total word-list decoder.

## Main definitions

There are no new definitions. The input count and bit bound are arbitrary unary computable
functions; the source word is an arbitrary polynomial-time function of the machine input.

## Main results

* `polyTimeComputable_encWords_decWords`: canonical reencoding is polynomial-time.
* `polyTimeComputable_decWords_getD`: total decoded-word lookup is polynomial-time.
* `polyTimeComputable_encode_normalizeMsgs`: bounded-slot normalization is polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity Turing

/-- Canonical reencoding is polynomial-time: if `raw` is polynomial-time, so is
`w ↦ BinArith.encWords (BinArith.decWords (raw w))`.
`PolyTimeComputable fun w => BinArith.encWords (BinArith.decWords (raw w))`. -/
theorem polyTimeComputable_encWords_decWords {raw : List Bool → List Bool}
    (hraw : PolyTimeComputable raw) :
    PolyTimeComputable fun w => BinArith.encWords (BinArith.decWords (raw w)) := by
  have hpre : PolyTimeComputable fun w => pairEncode [] (raw w) :=
    (polyTimeComputable_const []).pairEncode hraw
  refine ((BinArith.polyTimeComputable_mapW polyTimeComputable_pairSndD).comp hpre).congr ?_
  intro w
  simp only [Function.comp_apply, BinArith.mapW_pairEncode, pairSndD_pairEncode, List.map_id']

/-- Total decoded-word lookup is polynomial-time: if `raw` and the unary index `i` are
polynomial-time, so is `w ↦ (BinArith.decWords (raw w)).getD (i w) []`.
`PolyTimeComputable fun w => (BinArith.decWords (raw w)).getD (i w) []`. -/
theorem polyTimeComputable_decWords_getD {raw : List Bool → List Bool}
    (hraw : PolyTimeComputable raw) {i : List Bool → ℕ}
    (hi : PolyTimeComputable fun w => List.replicate (i w) true) :
    PolyTimeComputable fun w => (BinArith.decWords (raw w)).getD (i w) [] := by
  have hcanon := polyTimeComputable_encWords_decWords hraw
  refine (BinArith.polyTimeComputable_getW.comp (hi.pairEncode hcanon)).congr ?_
  intro w
  simp only [Function.comp_apply, BinArith.getW_pairEncode, List.length_replicate]

/-- Bounded-slot normalization is polynomial-time: if `p` and `B` are computable in unary
and `raw` is polynomial-time, then so is
`w ↦ Strategy.encodeMsgs (normalizeMsgs (p w) (B w) (raw w))`.
[PS10, Theorem 175.1, bounded phase-shape normalization].
`PolyTimeComputable fun w => Strategy.encodeMsgs (normalizeMsgs (p w) (B w) (raw w))`.

**Proof sketch.** Canonically reencode the total decoder's result through the generic word
map. The generic lookup host reads each requested slot, including empty defaults beyond the
end. Truncate that slot to the unary bit bound and emit its self-delimiting pair. The published
counted-emission host concatenates these chunks over the unary number of requested slots;
the resulting word is precisely the normalized list's encoding. -/
theorem polyTimeComputable_encode_normalizeMsgs {p B : List Bool → ℕ}
    {raw : List Bool → List Bool}
    (hp : PolyTimeComputable fun w => List.replicate (p w) true)
    (hB : PolyTimeComputable fun w => List.replicate (B w) true)
    (hraw : PolyTimeComputable raw) :
    PolyTimeComputable fun w => Strategy.encodeMsgs (normalizeMsgs (p w) (B w) (raw w)) := by
  -- Look up a total decoded slot at the emitter's unary counter.
  have hidx : PolyTimeComputable fun w => List.replicate (pairFstD w).length true :=
    EncodingMachines.unaryLength_poly polyTimeComputable_pairFstD
  have hlookup := polyTimeComputable_decWords_getD
    (hraw.comp polyTimeComputable_pairSndD) hidx
  -- Cap the payload and emit its self-delimiting message encoding.
  have hcap := EncodingMachines.truncate_poly hlookup (hB.comp polyTimeComputable_pairSndD)
  have hchunk : PolyTimeComputable fun w => pairEncode
      (((BinArith.decWords (raw (pairSndD w))).getD (pairFstD w).length []).take
        (B (pairSndD w))) [] :=
    hcap.pairEncode (polyTimeComputable_const [])
  -- The published counted emitter supplies exactly p slots.
  refine (ColMachines.polyTimeComputable_flatMap_range
    (E := fun w i => pairEncode (((BinArith.decWords (raw w)).getD i []).take (B w)) [])
    hchunk hp).congr ?_
  intro w
  simp only [normalizeMsgs_eq, encodeMsgs_eq_encWords, BinArith.encWords_def,
    List.flatMap_map]

end TCSlib.Cryptography.SequentialZK
