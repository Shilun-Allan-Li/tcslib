/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.Modular
import TCSlib.Cryptography.SIS.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary SIS inputs and fixed-width signed solver outputs

## Main definitions

* `TCSlib.Cryptography.SIS.encodeChallenge`: the row-major public matrix.
* `decodeSolution`: decode an exact-length sign-and-magnitude integer vector, rejecting
  every output whose total length differs from the prescribed length.
* `encodeSolution`: concatenate one sign-and-magnitude block for each integer coordinate.

## Main results

* `encodeChallenge_eq`, `decodeSolution_eq` expose the input encoding and output parser.
* `decodeSolution_of_length_ne`: a malformed output length is rejected.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.1.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Section 2.1 (binary-string machine inputs and outputs).

**Representation convention.** Input entries are fixed-width nonnegative representatives
of residues, in row-major order. Output coordinate `i` occupies one sign bit followed by
`magnitudeBits` magnitude bits, most significant bit first. Sign `true` means negative.
The output length must be exactly `P.columns * (magnitudeBits + 1)`. Negative zero is
accepted and decodes to zero, so the signed output representation is deliberately not
unique. This causes no ambiguity in the integer solution relation.

The parser is total, and malformed lengths return `none`. It does not itself test the
norm, nonzeroness or kernel equation: the concrete SIS success experiment tests all of
them. The asymptotic family requires a magnitude width sufficient for every valid bounded
solution. Decoder completeness, lengths and input faithfulness are explicit admitted
statements for the statement gate, rather than assumed correctness hypotheses.
-/

namespace TCSlib.Cryptography.SIS

/-- Encode the public SIS matrix [Pei16, Definition 4.1.1] in row-major order, using
the common modular representation. It retains every residue when
`P.modulus <= 2^width`. -/
def encodeChallenge (P : Parameters) (width : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus)) : List Bool :=
  Encoding.Modular.encodeMatrix width A

/-- `encodeChallenge P width A` is the common row-major `encodeMatrix width A`. -/
theorem encodeChallenge_eq (P : Parameters) (width : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus)) :
    encodeChallenge P width A = Encoding.Modular.encodeMatrix width A := rfl

/-- Decode a binary machine output as the integer vector required by SIS
[Pei16, Definition 4.1.1; PS10, Section 2.1]. Each coordinate is a sign bit (`true`
means negative) followed by a fixed-width nonnegative magnitude. Reject a wrong total
length. Both signs of zero decode to the same integer zero; the decoder does not claim
that the signed representation is unique. -/
def decodeSolution (P : Parameters) (magnitudeBits : ℕ) (w : List Bool) :
    Option (Fin P.columns → ℤ) :=
  if w.length = P.columns * (magnitudeBits + 1) then
    some (fun i =>
      let magnitude := NumberTheory.listToNat
        ((w.drop (i.val * (magnitudeBits + 1) + 1)).take magnitudeBits)
      if w.getD (i.val * (magnitudeBits + 1)) false then
        -(magnitude : ℤ)
      else
        (magnitude : ℤ))
  else none

/-- `decodeSolution P magnitudeBits w` is `none` for a wrong total length; otherwise
coordinate `i` is the signed magnitude in its block of `magnitudeBits + 1` bits. -/
theorem decodeSolution_eq (P : Parameters) (magnitudeBits : ℕ) (w : List Bool) :
    decodeSolution P magnitudeBits w =
      if w.length = P.columns * (magnitudeBits + 1) then
        some (fun i =>
          let magnitude := NumberTheory.listToNat
            ((w.drop (i.val * (magnitudeBits + 1) + 1)).take magnitudeBits)
          if w.getD (i.val * (magnitudeBits + 1)) false then
            -(magnitude : ℤ)
          else
            (magnitude : ℤ))
      else none := rfl

/-- If `w.length` is not `P.columns * (magnitudeBits + 1)`, then
`decodeSolution P magnitudeBits w = none`. -/
theorem decodeSolution_of_length_ne (P : Parameters) (magnitudeBits : ℕ) (w : List Bool)
    (h : w.length ≠ P.columns * (magnitudeBits + 1)) :
    decodeSolution P magnitudeBits w = none := by
  rw [decodeSolution_eq, if_neg h]

/-- Encode an integer solution candidate as one sign bit and a fixed-width magnitude
per coordinate. Sign `true` means negative, and zero is written with sign `false`.
Magnitudes are lossless when each is less than `2^magnitudeBits`; the underlying numeral
operation is total and truncates larger magnitudes. This is representation plumbing for
the integer vectors in [Pei16, Definition 4.1.1]. -/
def encodeSolution (P : Parameters) (magnitudeBits : ℕ) (z : Fin P.columns → ℤ) :
    List Bool :=
  (List.ofFn fun i => decide (z i < 0) ::
    Candidates.natToList magnitudeBits (z i).natAbs).flatten

/-- `encodeSolution` concatenates the negative-sign test followed by the fixed-width
absolute-value numeral for each coordinate in increasing order. -/
theorem encodeSolution_eq (P : Parameters) (magnitudeBits : ℕ) (z : Fin P.columns → ℤ) :
    encodeSolution P magnitudeBits z =
      (List.ofFn fun i => decide (z i < 0) ::
        Candidates.natToList magnitudeBits (z i).natAbs).flatten := rfl

/-- An encoded SIS matrix has exactly `dimension * columns * width` bits.

**Proof sketch.** Read `encodeChallenge_eq` and apply the common matrix-length statement. -/
theorem encodeChallenge_length (P : Parameters) (width : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus)) :
    (encodeChallenge P width A).length = P.dimension * P.columns * width := by
  sorry

/-- The SIS matrix encoding is injective when every modular entry fits in the width.

**Proof sketch.** Read `encodeChallenge_eq` and use the common matrix injectivity statement. -/
theorem encodeChallenge_injective (P : Parameters) (width : ℕ)
    (hwidth : P.modulus ≤ 2 ^ width) :
    Function.Injective (encodeChallenge P width) := by
  sorry

/-- The signed encoding has exactly one sign bit and `magnitudeBits` magnitude bits
per integer coordinate, including when there are no coordinates or zero magnitude bits.

**Proof sketch.** Every block is a singleton sign followed by a numeral of the prescribed
length; add those equal block lengths over all coordinates. -/
theorem encodeSolution_length (P : Parameters) (magnitudeBits : ℕ) (z : Fin P.columns → ℤ) :
    (encodeSolution P magnitudeBits z).length = P.columns * (magnitudeBits + 1) := by
  sorry

/-- Decoding a signed encoding recovers every coordinate whose magnitude fits.

**Proof sketch.** The length statement opens the decoder's successful branch. The
fixed-offset block slices recover each sign and numeral, the existing numeral round trip
recovers its magnitude, and the integer sign/absolute-value identities recover the integer.
The zero-coordinate and zero-magnitude-width cases are included. -/
theorem decodeSolution_encodeSolution (P : Parameters) (magnitudeBits : ℕ)
    (z : Fin P.columns → ℤ) (hfit : ∀ i, (z i).natAbs < 2 ^ magnitudeBits) :
    decodeSolution P magnitudeBits (encodeSolution P magnitudeBits z) = some z := by
  sorry

/-- Every valid SIS solution is representable in the prescribed signed format when
the squared-norm bound is less than `2^magnitudeBits` [Pei16, Definition 4.1.1,
squared-bound representation].

**Proof sketch.** A coordinate square is at most the total sum of squares, so a solution's
integer absolute coordinate is at most the natural squared-norm bound. The given strict
inequality makes each magnitude fit; apply `decodeSolution_encodeSolution`. -/
theorem decodeSolution_encodeSolution_of_isSolution (P : Parameters) (magnitudeBits : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (z : Fin P.columns → ℤ) (hsolution : IsSolution P A z)
    (hfit : P.sqNormBound < 2 ^ magnitudeBits) :
    decodeSolution P magnitudeBits (encodeSolution P magnitudeBits z) = some z := by
  sorry

end TCSlib.Cryptography.SIS
