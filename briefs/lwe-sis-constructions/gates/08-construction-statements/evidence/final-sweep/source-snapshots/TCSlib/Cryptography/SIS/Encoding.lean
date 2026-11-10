/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.Modular
import TCSlib.Cryptography.SIS.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

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
* The length, input injectivity and signed round-trip theorems establish faithful
  representation, including coverage of every solution under the prescribed norm bound.

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
solution. Decoder completeness, lengths and input faithfulness are proved below,
rather than stored as additional correctness hypotheses in the hardness assumption.
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
  rw [encodeChallenge_eq, Encoding.Modular.encodeMatrix_length]

/-- The SIS matrix encoding is injective when every modular entry fits in the width.

**Proof sketch.** Read `encodeChallenge_eq` and use the common matrix injectivity statement. -/
theorem encodeChallenge_injective (P : Parameters) (width : ℕ)
    (hwidth : P.modulus ≤ 2 ^ width) :
    Function.Injective (encodeChallenge P width) := by
  intro A B h
  apply Encoding.Modular.encodeMatrix_injective width hwidth
  simpa only [encodeChallenge_eq] using h

/-- The signed encoding has exactly one sign bit and `magnitudeBits` magnitude bits
per integer coordinate, including when there are no coordinates or zero magnitude bits.

**Proof sketch.** Every block is a singleton sign followed by a numeral of the prescribed
length; add those equal block lengths over all coordinates. -/
theorem encodeSolution_length (P : Parameters) (magnitudeBits : ℕ) (z : Fin P.columns → ℤ) :
    (encodeSolution P magnitudeBits z).length = P.columns * (magnitudeBits + 1) := by
  rw [encodeSolution_eq, List.length_flatten, ← List.ofFn_comp']
  simp only [List.length_cons, Candidates.length_natToList, List.ofFn_const,
    List.sum_replicate_nat]

/-- Decoding a signed encoding recovers every coordinate whose magnitude fits.

**Proof sketch.** The length statement opens the decoder's successful branch. The
fixed-offset block slices recover each sign and numeral, the existing numeral round trip
recovers its magnitude, and the integer sign/absolute-value identities recover the integer.
The zero-coordinate and zero-magnitude-width cases are included. -/
theorem decodeSolution_encodeSolution (P : Parameters) (magnitudeBits : ℕ)
    (z : Fin P.columns → ℤ) (hfit : ∀ i, (z i).natAbs < 2 ^ magnitudeBits) :
    decodeSolution P magnitudeBits (encodeSolution P magnitudeBits z) = some z := by
  let blocks : Fin P.columns → List Bool := fun i =>
    decide (z i < 0) :: Candidates.natToList magnitudeBits (z i).natAbs
  have hencoded :
      encodeSolution P magnitudeBits z = (List.ofFn blocks).flatten :=
    encodeSolution_eq P magnitudeBits z
  have hblockLength (j : Fin P.columns) :
      (blocks j).length = magnitudeBits + 1 := by
    change
      (decide (z j < 0) ::
        Candidates.natToList magnitudeBits (z j).natAbs).length =
          magnitudeBits + 1
    rw [List.length_cons, Candidates.length_natToList]
  have hmap :
      (List.ofFn blocks).map List.length =
        List.replicate P.columns (magnitudeBits + 1) := by
    calc
      _ = List.ofFn (fun j => (blocks j).length) :=
        List.map_ofFn blocks List.length
      _ = List.ofFn (fun _ : Fin P.columns => magnitudeBits + 1) :=
        congrArg List.ofFn (funext hblockLength)
      _ = _ := List.ofFn_const P.columns (magnitudeBits + 1)
  have hprefix (j : ℕ) (hj : j ≤ P.columns) :
      (((List.ofFn blocks).map List.length).take j).sum =
        j * (magnitudeBits + 1) := by
    rw [hmap, List.take_replicate, Nat.min_eq_left hj, List.sum_replicate_nat]
  rw [decodeSolution_eq, encodeSolution_length, if_pos rfl]
  apply congrArg some
  funext i
  have hblock :
      ((List.ofFn blocks).flatten.drop
        (i.val * (magnitudeBits + 1))).take (magnitudeBits + 1) =
          blocks i := by
    have h := List.drop_take_succ_flatten_eq_getElem
      (List.ofFn blocks) i.val
      (by simpa only [List.length_ofFn] using i.isLt)
    rw [hprefix (i.val + 1) (Nat.succ_le_of_lt i.isLt),
      hprefix i.val (Nat.le_of_lt i.isLt),
      List.drop_take, Nat.add_mul, Nat.one_mul,
      Nat.add_sub_cancel_left] at h
    simpa only [List.getElem_ofFn] using h
  have hsign :
      (List.ofFn blocks).flatten.getD
        (i.val * (magnitudeBits + 1)) false =
          decide (z i < 0) := by
    have h := congrArg (fun xs : List Bool => xs.getD 0 false) hblock
    simpa only [List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (Nat.zero_lt_succ magnitudeBits),
      List.getElem?_drop, Nat.add_zero, blocks,
      List.getElem?_cons_zero, Option.getD_some] using h
  have hmagnitude :
      ((List.ofFn blocks).flatten.drop
        (i.val * (magnitudeBits + 1) + 1)).take magnitudeBits =
          Candidates.natToList magnitudeBits (z i).natAbs := by
    have h := congrArg (fun xs : List Bool => xs.drop 1) hblock
    simpa only [List.drop_take, List.drop_drop, Nat.add_sub_cancel,
      blocks, List.drop_succ_cons, List.drop_zero] using h
  rw [hencoded, hsign, hmagnitude, Candidates.listToNat_natToList (hfit i)]
  change
    (if decide (z i < 0) then -((z i).natAbs : ℤ)
      else ((z i).natAbs : ℤ)) = z i
  by_cases hneg : z i < 0
  · rw [if_pos (decide_eq_true hneg),
      Int.ofNat_natAbs_of_nonpos (le_of_lt hneg), Int.neg_neg]
  · have hd : decide (z i < 0) ≠ true := by
      intro h
      exact hneg (of_decide_eq_true h)
    rw [if_neg hd]
    exact Int.natAbs_of_nonneg (le_of_not_gt hneg)

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
  apply decodeSolution_encodeSolution P magnitudeBits z
  intro i
  have hnorm := ((isSolution_iff P A z).mp hsolution).2.1
  have hcoordinate : z i ^ 2 ≤ ∑ j, z j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
  have hbound : ((z i).natAbs : ℤ) ≤ (P.sqNormBound : ℤ) :=
    (Int.natAbs_le_self_sq (z i)).trans (hcoordinate.trans hnorm)
  exact lt_of_le_of_lt (Int.ofNat_le.mp hbound) hfit

end TCSlib.Cryptography.SIS
