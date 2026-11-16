/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.NormalizationMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Canonical phase-view normalization

A one-phase simulator outputs an arbitrary word. For sequential composition, validate its
metadata, empty wrapper tape, and canonical message-list encoding before extracting its
messages. A malformed view contributes empty slots. The bounded-slot normalization then
supplies exactly the prescribed number of messages, each of bounded length, without any
assumption on the simulator's output shape. [PS10, Theorem 175.1].

## Main definitions

* `phaseViewPayload x z raw`: the message encoding of a canonical view with fields `x,z,[]`,
  or `[]` when `raw` fails validation.
* `normalizePhaseMsgs x z p B raw`: the validated payload normalized to `p` slots of `B` bits.

## Main results

* `phaseViewPayload_of_encode`: validation fixes every canonical view with the known fields.
* `normalizePhaseMsgs_of_encode`: normalization fixes canonical bounded real views.
* `normalizePhaseMsgs_of_ne`: malformed phase views yield exactly the requested empty slots.
* `length_normalizePhaseMsgs`, `length_le_of_mem_normalizePhaseMsgs`,
  `length_encodeMsgs_normalizePhaseMsgs_le`: count, message-length and encoded-size bounds.
* `polyTimeComputable_phaseViewPayload`, `polyTimeComputable_encode_normalizePhaseMsgs`:
  canonical validation and encoded bounded normalization are polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity Turing

/-- The validated message payload is `pairSndD (pairSndD raw)` when `raw` is exactly the
encoding of `⟨x,z,[],decWords (pairSndD (pairSndD raw))⟩`, and is `[]` otherwise. This checks
the known common input, auxiliary input, empty wrapper tape, and canonical message encoding.
[PS10, Theorem 175.1, canonical phase-view fallback].
`phaseViewPayload x z raw = if raw = View.encode ⟨x, z, [], BinArith.decWords (pairSndD (pairSndD
raw))⟩ then pairSndD (pairSndD raw) else []`. -/
def phaseViewPayload (x z raw : List Bool) : List Bool :=
  if raw = View.encode ⟨x, z, [], BinArith.decWords (pairSndD (pairSndD raw))⟩ then
    pairSndD (pairSndD raw)
  else []

/-- The payload formula is `phaseViewPayload x z raw = if raw = View.encode
⟨x,z,[],decWords (pairSndD (pairSndD raw))⟩ then pairSndD (pairSndD raw) else []`. -/
theorem phaseViewPayload_eq (x z raw : List Bool) :
    phaseViewPayload x z raw =
      if raw = View.encode ⟨x, z, [], BinArith.decWords (pairSndD (pairSndD raw))⟩ then
        pairSndD (pairSndD raw)
      else [] := rfl

/-- Canonical phase-view normalization validates `raw` for the known fields `x,z,[]`, then
supplies exactly `p` slots, each truncated to `B` bits, with empty defaults. A malformed view
therefore supplies `p` empty messages. [PS10, Theorem 175.1, phase-shape normalization].
`normalizePhaseMsgs x z p B raw = normalizeMsgs p B (phaseViewPayload x z raw)`. -/
def normalizePhaseMsgs (x z : List Bool) (p B : ℕ) (raw : List Bool) : List (List Bool) :=
  normalizeMsgs p B (phaseViewPayload x z raw)

/-- `normalizePhaseMsgs x z p B raw = normalizeMsgs p B (phaseViewPayload x z raw)`. -/
theorem normalizePhaseMsgs_eq (x z : List Bool) (p B : ℕ) (raw : List Bool) :
    normalizePhaseMsgs x z p B raw = normalizeMsgs p B (phaseViewPayload x z raw) := rfl

/-- Validation fixes every canonical view with the prescribed fields:
`phaseViewPayload x z (View.encode ⟨x,z,[],h⟩) = Strategy.encodeMsgs h`. -/
theorem phaseViewPayload_of_encode (x z : List Bool) (h : List (List Bool)) :
    phaseViewPayload x z (View.encode ⟨x, z, [], h⟩) = Strategy.encodeMsgs h := by
  simp only [phaseViewPayload_eq, View.encode_mk, pairSndD_pairEncode,
    encodeMsgs_eq_encWords, BinArith.decWords_encWords, if_true]

/-- Failed validation produces an empty payload: if `raw` differs from the canonical view
`⟨x,z,[],decWords (pairSndD (pairSndD raw))⟩`, then `phaseViewPayload x z raw = []`. -/
theorem phaseViewPayload_of_ne (x z raw : List Bool)
    (hraw : raw ≠ View.encode ⟨x, z, [], BinArith.decWords (pairSndD (pairSndD raw))⟩) :
    phaseViewPayload x z raw = [] := by
  rw [phaseViewPayload_eq, if_neg hraw]

/-- Phase-view normalization fixes a canonical bounded real view:
`normalizePhaseMsgs x z p B (View.encode ⟨x,z,[],h⟩) = h` if `h.length = p` and
`∀ m ∈ h, m.length ≤ B`. -/
theorem normalizePhaseMsgs_of_encode (x z : List Bool) (p B : ℕ) (h : List (List Bool))
    (hp : h.length = p) (hB : ∀ m ∈ h, m.length ≤ B) :
    normalizePhaseMsgs x z p B (View.encode ⟨x, z, [], h⟩) = h := by
  rw [normalizePhaseMsgs_eq, phaseViewPayload_of_encode]
  exact normalizeMsgs_encodeMsgs p B h hp hB

/-- Every phase-view normalization has exactly `p` slots:
`(normalizePhaseMsgs x z p B raw).length = p`. -/
theorem length_normalizePhaseMsgs (x z : List Bool) (p B : ℕ) (raw : List Bool) :
    (normalizePhaseMsgs x z p B raw).length = p := by
  rw [normalizePhaseMsgs_eq]
  exact length_normalizeMsgs p B _

/-- Each normalized phase message has at most `B` bits:
`m ∈ normalizePhaseMsgs x z p B raw → m.length ≤ B`. -/
theorem length_le_of_mem_normalizePhaseMsgs (x z : List Bool) (p B : ℕ) (raw : List Bool)
    {m : List Bool} (hm : m ∈ normalizePhaseMsgs x z p B raw) : m.length ≤ B := by
  rw [normalizePhaseMsgs_eq] at hm
  exact length_le_of_mem_normalizeMsgs p B _ hm

/-- The normalized phase message encoding is bounded by
`(Strategy.encodeMsgs (normalizePhaseMsgs x z p B raw)).length ≤ p * (2 * B + 2)`. -/
theorem length_encodeMsgs_normalizePhaseMsgs_le (x z : List Bool) (p B : ℕ) (raw : List Bool) :
    (Strategy.encodeMsgs (normalizePhaseMsgs x z p B raw)).length ≤ p * (2 * B + 2) := by
  rw [normalizePhaseMsgs_eq]
  exact length_encodeMsgs_normalizeMsgs_le p B _

/-- A malformed phase view yields exactly `p` empty messages:
`normalizePhaseMsgs x z p B raw = List.replicate p []` when validation fails. -/
theorem normalizePhaseMsgs_of_ne (x z : List Bool) (p B : ℕ) (raw : List Bool)
    (hraw : raw ≠ View.encode ⟨x, z, [], BinArith.decWords (pairSndD (pairSndD raw))⟩) :
    normalizePhaseMsgs x z p B raw = List.replicate p [] := by
  rw [normalizePhaseMsgs_eq, phaseViewPayload_of_ne x z raw hraw, normalizeMsgs_eq,
    BinArith.decWords_nil]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none,
    List.take_nil, List.map_const', List.length_range]

/-- Canonical phase-view validation is polynomial-time: polynomial-time `x`, `z` and `raw`
give a polynomial-time map `w ↦ phaseViewPayload (x w) (z w) (raw w)`.
`PolyTimeComputable fun w => phaseViewPayload (x w) (z w) (raw w)`.

**Proof sketch.** Extract the candidate message word through two pair projections, and
canonically reencode its total decoding through the word-map host. Pair this encoding with
the known common input, auxiliary input, and empty wrapper tape. The public word-equality
machine checks whether that reconstructed view equals the original word; a conditional
machine returns the extracted payload on success and the empty word on failure. -/
theorem polyTimeComputable_phaseViewPayload {x z raw : List Bool → List Bool}
    (hx : PolyTimeComputable x) (hz : PolyTimeComputable z) (hraw : PolyTimeComputable raw) :
    PolyTimeComputable fun w => phaseViewPayload (x w) (z w) (raw w) := by
  -- Reconstruct the canonical candidate with the prescribed metadata and tape.
  have hpayload : PolyTimeComputable fun w => pairSndD (pairSndD (raw w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hraw)
  have hcanonical := polyTimeComputable_encWords_decWords hpayload
  have hview : PolyTimeComputable fun w => pairEncode (pairEncode (x w) (z w))
      (pairEncode [] (BinArith.encWords (BinArith.decWords (pairSndD (pairSndD (raw w)))))) :=
    (hx.pairEncode hz).pairEncode ((polyTimeComputable_const []).pairEncode hcanonical)
  -- Compare the candidate with the original and select the validated payload.
  have htest := BinArith.polyTimeComputable_eqW.comp (hraw.pairEncode hview)
  refine (polyTimeComputable_ite htest hpayload (polyTimeComputable_const [])).congr ?_
  intro w
  simp only [phaseViewPayload_eq, BinArith.eqW_pairEncode,
    decide_eq_true_eq, View.encode_mk, encodeMsgs_eq_encWords]

/-- Canonical bounded phase-view normalization is polynomial-time: polynomial-time `x`, `z`
and `raw`, and unary-computable `p` and `B`, give a polynomial-time map
`w ↦ Strategy.encodeMsgs (normalizePhaseMsgs (x w) (z w) (p w) (B w) (raw w))`.
[PS10, Theorem 175.1, bounded canonical phase-view normalization].
`PolyTimeComputable fun w => Strategy.encodeMsgs (normalizePhaseMsgs (x w) (z w) (p w) (B w) (raw
w))`. -/
theorem polyTimeComputable_encode_normalizePhaseMsgs {x z raw : List Bool → List Bool}
    {p B : List Bool → ℕ}
    (hx : PolyTimeComputable x) (hz : PolyTimeComputable z) (hraw : PolyTimeComputable raw)
    (hp : PolyTimeComputable fun w => List.replicate (p w) true)
    (hB : PolyTimeComputable fun w => List.replicate (B w) true) :
    PolyTimeComputable fun w =>
      Strategy.encodeMsgs (normalizePhaseMsgs (x w) (z w) (p w) (B w) (raw w)) := by
  have hpayload := polyTimeComputable_phaseViewPayload hx hz hraw
  refine (polyTimeComputable_encode_normalizeMsgs hp hB hpayload).congr ?_
  intro w
  rw [normalizePhaseMsgs_eq]

end TCSlib.Cryptography.SequentialZK
