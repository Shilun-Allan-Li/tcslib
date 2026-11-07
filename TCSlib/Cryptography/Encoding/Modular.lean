/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Candidates.Arithmetic
import Mathlib.Data.Matrix.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fixed-width encodings of modular vectors and matrices

## Main definitions

* `TCSlib.Cryptography.Encoding.Modular.encodeVector`: concatenate the fixed-width
  binary numerals of a residue vector in increasing coordinate order.
* `encodeMatrix`: concatenate the encoded rows of a matrix in increasing row order.

## Main results

* `encodeVector_eq`, `encodeMatrix_eq` expose the two concatenations.
* The length and injectivity statements specify their representation obligations.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definitions 4.1.1 and 4.2.3 (the modular inputs being represented).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Section 2.1 (binary-string machine inputs).

**Representation convention.** These encodings are repository plumbing, rather than
additional lattice assumptions. Each residue uses its representative in `[0,q)`, written
most significant bit first by the existing public `Candidates.natToList`. A width `k`
represents every residue without truncation when `q <= 2^k`. The definitions are total at
smaller widths, where the numeral operation keeps only low-order bits; consumers must
supply the width bound before using faithfulness. The LWE and SIS asymptotic families
carry that bound. No polynomial-time machine implementation is asserted here.

The vector length is `length * width` and the matrix length is `rows * columns * width`.
Length and injectivity are statement-gate obligations below; their proofs are admitted
pending that gate. The defining equations are the only proved readers in this module.
-/

namespace TCSlib.Cryptography.Encoding.Modular

/-- Encode a modular vector in increasing coordinate order, using the public fixed-width
numeral operation. For `q <= 2^width` no residue is truncated. This is the binary
representation convention for the vectors in [Pei16, Definitions 4.1.1 and 4.2.3]. -/
def encodeVector {q length : ℕ} [NeZero q] (width : ℕ)
    (v : Fin length → ZMod q) : List Bool :=
  (List.ofFn fun i => Candidates.natToList width (v i).val).flatten

/-- `encodeVector width v` concatenates `natToList width (v i).val` over coordinates
`i` in increasing order. -/
theorem encodeVector_eq {q length : ℕ} [NeZero q] (width : ℕ)
    (v : Fin length → ZMod q) :
    encodeVector width v =
      (List.ofFn fun i => Candidates.natToList width (v i).val).flatten := rfl

/-- Encode a modular matrix row by row, with columns increasing within each row.
For `q <= 2^width` no entry is truncated. This fixes the binary representation of the
matrices in [Pei16, Definitions 4.1.1 and 4.2.3]. -/
def encodeMatrix {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (A : Matrix (Fin rows) (Fin columns) (ZMod q)) : List Bool :=
  (List.ofFn fun i => encodeVector width (A i)).flatten

/-- `encodeMatrix width A` concatenates `encodeVector width (A i)` over rows `i`
in increasing order. -/
theorem encodeMatrix_eq {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (A : Matrix (Fin rows) (Fin columns) (ZMod q)) :
    encodeMatrix width A = (List.ofFn fun i => encodeVector width (A i)).flatten := rfl

/-- A vector encoding has exactly `length * width` bits.

**Proof sketch.** Every numeral has length `width` by the existing numeral-length
lemma. Sum these equal lengths over the `length` coordinate blocks. -/
theorem encodeVector_length {q length : ℕ} [NeZero q] (width : ℕ)
    (v : Fin length → ZMod q) :
    (encodeVector width v).length = length * width := by
  sorry

/-- A matrix encoding has exactly `rows * columns * width` bits.

**Proof sketch.** Each encoded row has `columns * width` bits by
`encodeVector_length`; concatenate `rows` such blocks and reassociate multiplication. -/
theorem encodeMatrix_length {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (A : Matrix (Fin rows) (Fin columns) (ZMod q)) :
    (encodeMatrix width A).length = rows * columns * width := by
  sorry

/-- Fixed-width vector encoding is injective when every residue fits in that width.

**Proof sketch.** Cut equal encoded strings into their fixed-width coordinate blocks.
The existing numeral round-trip lemma recovers each representative, since it is less
than `q` and `q <= 2^width`. Equal representatives give equal residues at every coordinate.
The zero-coordinate and modulus-one/zero-width cases are included. -/
theorem encodeVector_injective {q length : ℕ} [NeZero q] (width : ℕ)
    (hwidth : q ≤ 2 ^ width) :
    Function.Injective (encodeVector (q := q) (length := length) width) := by
  sorry

/-- Fixed-width row-major matrix encoding is injective when every residue fits.

**Proof sketch.** Cut equal encodings into equal fixed-length row blocks using
`encodeVector_length`, then apply `encodeVector_injective` to every row. Empty row or
column sets represent the unique matrix on an empty index product. -/
theorem encodeMatrix_injective {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (hwidth : q ≤ 2 ^ width) :
    Function.Injective (encodeMatrix (q := q) (rows := rows) (columns := columns) width) := by
  sorry

end TCSlib.Cryptography.Encoding.Modular
