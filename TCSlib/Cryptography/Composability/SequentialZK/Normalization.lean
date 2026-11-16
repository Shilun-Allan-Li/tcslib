/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Complexity.ClassP.BinaryArith.Words

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bounded message slots for sequential zero-knowledge simulation

A phase simulator can output an arbitrary word. The message-slot normalization reads that word
as an encoded list, retains exactly the requested number of slots, truncates every message to
the requested bit bound, and supplies empty messages for missing entries. This is the bounded
message-list part of the normalization in [PS10, Theorem 175.1]. Validation of view metadata
and the choice of a fallback view are separate operations.

## Main definitions

* `normalizeMsgs p B raw`: exactly `p` decoded message slots, each truncated to `B` bits.

## Main results

* `encodeMsgs_eq_encWords`: the interaction and generic word-list encodings agree.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity Turing

/-- The two message-list encodings agree: `Strategy.encodeMsgs h = BinArith.encWords h`. -/
theorem encodeMsgs_eq_encWords (h : List (List Bool)) :
    Strategy.encodeMsgs h = BinArith.encWords h := by
  induction h with
  | nil => rw [Strategy.encodeMsgs_nil, BinArith.encWords_nil]
  | cons m h ih => rw [Strategy.encodeMsgs_cons, BinArith.encWords_cons, ih]

/-- Bounded message slots: `normalizeMsgs p B raw` is the list of the first `p` words decoded
from `raw`, with missing words replaced by `[]` and every word truncated to `B` bits.
[PS10, Theorem 175.1, bounded phase-shape normalization].
`normalizeMsgs p B raw = (List.range p).map (fun i => ((BinArith.decWords raw).getD i []).take
B)`. -/
def normalizeMsgs (p B : ℕ) (raw : List Bool) : List (List Bool) :=
  (List.range p).map fun i => ((BinArith.decWords raw).getD i []).take B

/-- The slot formula is
`normalizeMsgs p B raw = (List.range p).map (fun i => ((decWords raw).getD i []).take B)`. -/
theorem normalizeMsgs_eq (p B : ℕ) (raw : List Bool) :
    normalizeMsgs p B raw =
      (List.range p).map (fun i => ((BinArith.decWords raw).getD i []).take B) := rfl

/-- Normalization always supplies exactly the requested number of slots:
`(normalizeMsgs p B raw).length = p`. -/
theorem length_normalizeMsgs (p B : ℕ) (raw : List Bool) :
    (normalizeMsgs p B raw).length = p := by
  rw [normalizeMsgs_eq, List.length_map, List.length_range]

/-- Every normalized slot has at most `B` bits:
`m ∈ normalizeMsgs p B raw → m.length ≤ B`. -/
theorem length_le_of_mem_normalizeMsgs (p B : ℕ) (raw : List Bool) {m : List Bool}
    (hm : m ∈ normalizeMsgs p B raw) : m.length ≤ B := by
  rw [normalizeMsgs_eq] at hm
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
  rw [List.length_take]
  exact Nat.min_le_left _ _

/-- Normalization fixes an encoded list with `p` slots and messages of at most `B` bits:
`normalizeMsgs p B (Strategy.encodeMsgs h) = h` if `h.length = p` and
`∀ m ∈ h, m.length ≤ B`. -/
theorem normalizeMsgs_encodeMsgs (p B : ℕ) (h : List (List Bool))
    (hp : h.length = p) (hB : ∀ m ∈ h, m.length ≤ B) :
    normalizeMsgs p B (Strategy.encodeMsgs h) = h := by
  rw [normalizeMsgs_eq, encodeMsgs_eq_encWords, BinArith.decWords_encWords]
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, hp]
  · intro i hi hi'
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi', Option.getD_some]
    exact List.take_of_length_le (hB _ (List.getElem_mem hi'))

/-- The encoding of the normalized slots has the bound
`(Strategy.encodeMsgs (normalizeMsgs p B raw)).length ≤ p * (2 * B + 2)`. -/
theorem length_encodeMsgs_normalizeMsgs_le (p B : ℕ) (raw : List Bool) :
    (Strategy.encodeMsgs (normalizeMsgs p B raw)).length ≤ p * (2 * B + 2) := by
  rw [encodeMsgs_eq_encWords]
  calc
    (BinArith.encWords (normalizeMsgs p B raw)).length ≤
        (normalizeMsgs p B raw).length * (2 * B + 2) :=
      BinArith.length_encWords_le _ B fun m hm => length_le_of_mem_normalizeMsgs p B raw hm
    _ = p * (2 * B + 2) := by rw [length_normalizeMsgs]

end TCSlib.Cryptography.SequentialZK
