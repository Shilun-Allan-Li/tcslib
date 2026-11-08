/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.Modular
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Canonical parsing of modular vectors and row-major matrices

## Main definitions

* `decodeVector`: check total length and each representative before casting residues.
* `decodeMatrix`: reuse vector parsing and the public row-major finite-product equivalence.

## Main results

The complete equations and rejection cases read the parsers. The round trips are
statement-phase obligations: parsing an encoding needs width coverage; re-encoding
a successful parse is exact without a width hypothesis.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definitions 4.1.1 and 4.2.3 (the represented modular objects).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Section 2.1 (binary-string machine representations).

These parsers are representation glue, not new lattice theorems. They use the audited
MSB-first encoders and the existing numeral reader. Modulus one, zero widths and empty
dimensions are supported; no division by a block width occurs. Efficient machines are
a separate obligation. Wrong lengths and noncanonical representatives are rejected.
-/

namespace TCSlib.Cryptography.Encoding.Modular

open TCSlib.Cryptography.NumberTheory (listToNat)

/-- Parse exactly `length` width-bit residue representatives, rejecting a wrong total
length or any representative at least `q`. This is the canonical inverse interface
for the encodings of the inputs in [Pei16, Definitions 4.1.1 and 4.2.3]. -/
def decodeVector {q length : ℕ} [NeZero q] (width : ℕ) (w : List Bool) :
    Option (Fin length → ZMod q) :=
  if w.length = length * width ∧
      ∀ i : Fin length, listToNat ((w.drop (i.val * width)).take width) < q then
    some (fun i => (listToNat ((w.drop (i.val * width)).take width) : ZMod q))
  else none

/-- Vector parsing checks the exact total length and every chunk's value before
returning its coordinatewise cast; either failed check returns `none`. -/
theorem decodeVector_eq {q length : ℕ} [NeZero q] (width : ℕ) (w : List Bool) :
    decodeVector (q := q) (length := length) width w =
      if w.length = length * width ∧
          ∀ i : Fin length, listToNat ((w.drop (i.val * width)).take width) < q then
        some (fun i => (listToNat ((w.drop (i.val * width)).take width) : ZMod q))
      else none := rfl

/-- A word with the wrong total vector length is rejected. -/
theorem decodeVector_of_length_ne {q length : ℕ} [NeZero q] (width : ℕ)
    (w : List Bool) (h : w.length ≠ length * width) :
    decodeVector (q := q) (length := length) width w = none := by
  rw [decodeVector_eq, if_neg (fun hguard => h hguard.1)]

/-- A word with a coordinate representative outside `[0,q)` is rejected. -/
theorem decodeVector_of_outOfRange {q length : ℕ} [NeZero q] (width : ℕ)
    (w : List Bool) (i : Fin length)
    (h : q ≤ listToNat ((w.drop (i.val * width)).take width)) :
    decodeVector (q := q) (length := length) width w = none := by
  rw [decodeVector_eq, if_neg (fun hguard => (not_lt_of_ge h) (hguard.2 i))]

/-- Parsing a vector's encoding returns that vector when every residue fits.

**Proof sketch.** The audited length equation opens the length guard. Recover each
fixed-width block using public flatten/slicing lemmas, read its numeral through the
existing round trip, and use the residue representative bound to open the range guard.
The cast of each representative equals its residue. Width zero needs no cancellation. -/
theorem decodeVector_encodeVector {q length : ℕ} [NeZero q] (width : ℕ)
    (hwidth : q ≤ 2 ^ width) (v : Fin length → ZMod q) :
    decodeVector width (encodeVector width v) = some v := by
  sorry

/-- Re-encoding any successful vector parse gives the exact original word.
No global width-coverage hypothesis is required.

**Proof sketch.** A successful parse supplies exact length and in-range chunk values.
Their casts have those same representatives. Each chunk has width bits, so the existing
numeral writing round trip recovers it; concatenating the chunks recovers the word. -/
theorem encodeVector_decodeVector {q length : ℕ} [NeZero q] (width : ℕ)
    (w : List Bool) (v : Fin length → ZMod q) (h : decodeVector width w = some v) :
    encodeVector width v = w := by
  sorry

/-- Parse a row-major matrix by reusing vector parsing on `rows * columns` entries
and the public finite-product equivalence. All vector rejection rules are retained. -/
def decodeMatrix {q rows columns : ℕ} [NeZero q] (width : ℕ) (w : List Bool) :
    Option (Matrix (Fin rows) (Fin columns) (ZMod q)) :=
  (decodeVector (q := q) (length := rows * columns) width w).map
    (fun v i j => v (finProdFinEquiv (i, j)))

/-- Matrix parsing maps a successful vector parse through row-major finite-product
indexing; an unsuccessful vector parse remains `none`. -/
theorem decodeMatrix_eq {q rows columns : ℕ} [NeZero q] (width : ℕ) (w : List Bool) :
    decodeMatrix (q := q) (rows := rows) (columns := columns) width w =
      (decodeVector (q := q) (length := rows * columns) width w).map
        (fun v i j => v (finProdFinEquiv (i, j))) := rfl

/-- A word with the wrong total row-major matrix length is rejected. -/
theorem decodeMatrix_of_length_ne {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (w : List Bool) (h : w.length ≠ rows * columns * width) :
    decodeMatrix (q := q) (rows := rows) (columns := columns) width w = none := by
  rw [decodeMatrix_eq, decodeVector_of_length_ne width w h]
  rfl

/-- A matrix word containing an out-of-range entry is rejected.

**Proof sketch.** The public finite-product equivalence places `(i,j)` at index
`i * columns + j`; apply vector rejection at that index, then read `decodeMatrix_eq`. -/
theorem decodeMatrix_of_outOfRange {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (w : List Bool) (i : Fin rows) (j : Fin columns)
    (h : q ≤ listToNat ((w.drop ((i.val * columns + j.val) * width)).take width)) :
    decodeMatrix (q := q) (rows := rows) (columns := columns) width w = none := by
  sorry

/-- Parsing a row-major encoding returns the original matrix when every residue fits.

**Proof sketch.** Identify the row-major concatenation with its flattened finite-product
vector, apply the vector round trip, and use the finite-product equivalence at each entry. -/
theorem decodeMatrix_encodeMatrix {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (hwidth : q ≤ 2 ^ width) (A : Matrix (Fin rows) (Fin columns) (ZMod q)) :
    decodeMatrix width (encodeMatrix width A) = some A := by
  sorry

/-- Re-encoding a successful matrix parse gives the exact original word, including
empty row or column sets, without a global width-coverage hypothesis.

**Proof sketch.** Recover the successful vector parse, apply the vector writing round
trip, and identify row-major finite-product flattening with `encodeMatrix`. -/
theorem encodeMatrix_decodeMatrix {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (w : List Bool) (A : Matrix (Fin rows) (Fin columns) (ZMod q))
    (h : decodeMatrix width w = some A) : encodeMatrix width A = w := by
  sorry

end TCSlib.Cryptography.Encoding.Modular
