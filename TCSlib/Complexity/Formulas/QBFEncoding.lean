/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.QBF
import TCSlib.Complexity.Formulas.CNFEncoding
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary encoding of quantified Boolean formulas

The serialization layer for `Complexity.QBF`, mirroring the chapter-2 CNF
conventions (`TCSlib.Complexity.Formulas.CNFEncoding`): a self-delimiting
pair of the quantifier prefix (one bit per quantifier, `true` for `∃`) and
the matrix's LL(1) serialization, with a total `decode` whose fallback is the
closed trivial formula. Phase P4.3 of `AroraBarakChapters3-4Plan.md`; the
language `TQBF` (`TCSlib.Complexity.ClassPSPACE.TQBF`) is defined over this
decoding.

## Conventions

* `encode Q := Turing.pairEncode (prefix bits) (CNF.serialize Q.matrix)` —
  the campaign's aligned pairing, so one aligned parse recovers both
  components.
* `decode` totalizes with the fallback `⟨[], CNF.fallback⟩` (empty prefix,
  empty matrix) on strings that fail the pair parse; the matrix component
  reuses `CNF.decode`'s own fallback behavior. The fallback formula is
  **true** (the empty CNF evaluates `true`), so non-well-formed strings lie
  **in** `TQBF` — the same polarity as the chapter-2 `SAT` fallback
  convention, recorded there and here.

## Main definitions

* `Complexity.QBF.encode`, `Complexity.QBF.decode` — serialization and total
  decoding.

## Main results (sorried; phase-P4.3 statement)

* `Complexity.QBF.decode_encode` — decoding inverts encoding.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2; representation conventions as in
  §2.3's footnote 3.)
-/

namespace Complexity.QBF

open Std.Sat (CNF)
open Turing

/-- One bit per quantifier: `true` for `∃`, `false` for `∀`. -/
def quantBit : Quant → Bool
  | .ex => true
  | .all => false

/-- The quantifier of a bit, inverse to `Complexity.QBF.quantBit`. -/
def quantOfBit (b : Bool) : Quant :=
  if b then .ex else .all

/-- **Serialize a QBF**: the aligned pair of the prefix bits and the
chapter-2 matrix serialization. -/
def encode (Q : QBF) : List Bool :=
  pairEncode (Q.quants.map quantBit) (CNF.serialize Q.matrix)

/-- **Total decoding** with the closed trivial fallback: parse the aligned
pair, read the prefix bitwise, decode the matrix by the chapter-2 total
decoder; strings failing the pair parse decode to `⟨[], CNF.fallback⟩`
(which is **true** — the `SAT`-polarity fallback convention, see the module
docstring). -/
def decode (x : List Bool) : QBF :=
  match pairDecode x with
  | some (q, m) => ⟨q.map quantOfBit, CNF.decode m⟩
  | none => ⟨[], CNF.fallback⟩

/-- **Decoding inverts encoding** (spec, fill pending — phase P4.3): every
serialized formula decodes to itself.

**Proof sketch.** `Turing.pairDecode_pairEncode` splits the pair;
`quantOfBit ∘ quantBit = id` by cases (`List.map_map` and `List.map_id`);
`CNF.decode_serialize` (chapter 2) recovers the matrix. -/
theorem decode_encode (Q : QBF) : decode (encode Q) = Q := by
  sorry

end Complexity.QBF
