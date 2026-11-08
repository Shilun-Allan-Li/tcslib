/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.List.Basic

/-!
# The unary code of a natural number

The self-delimiting code `1ᵏ0` of a natural number `k`, and its parser.  Every circuit
description of the library writes its numbers this way: the formula encoding of
`Encoding.lean` (for `CKT-SAT`, [AB09, Def 6.9]), the book-model description
`BoolCircuit.DAGCircuit.encode` of `Uniform.lean` ([AB09, Def 6.12]), and its parser
`BoolCircuit.decodeDAG` in `DAGCircuitSatLang.lean`.

## Main definitions

* `BoolCircuit.encodeNat` — `k ↦ 1ᵏ0`.
* `BoolCircuit.decodeNat` — read one unary number off the front of a bit string.

## Main results

* `BoolCircuit.decodeNat_encodeNat` — reading back a code returns its number and the
  untouched rest.

## Divergences from [AB09]

* [AB09] fixes no representation of numbers inside circuit descriptions.  Unary costs a
  polynomial factor over binary (`O(n)` rather than `O(log n)` bits for an index below
  `n`), which every polynomial bound downstream absorbs.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1.2 and §6.2: string descriptions of circuits.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

/-- The unary code `1ᵏ0` of a natural number: `k` `true`s terminated by a `false`. -/
def encodeNat (k : ℕ) : List Bool := List.replicate k true ++ [false]

/-- Read a unary number `1ᵏ0` (`BoolCircuit.encodeNat`) off the front of a string,
returning it and the rest; `none` if the string ends before the terminating `0`. -/
def decodeNat : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: r => some (0, r)
  | true :: r => (decodeNat r).map fun p => (p.1 + 1, p.2)

/-- Reading back a unary code returns its number and the untouched rest. -/
theorem decodeNat_encodeNat (k : ℕ) (r : List Bool) :
    decodeNat (encodeNat k ++ r) = some (k, r) := by
  induction k with
  | zero => simp [encodeNat, decodeNat]
  | succ k ih =>
    have h : encodeNat (k + 1) ++ r = true :: (encodeNat k ++ r) := by
      simp [encodeNat, List.replicate_succ]
    rw [h, decodeNat, ih]
    rfl

end BoolCircuit
