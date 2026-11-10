/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.ModularDecode
import TCSlib.InformationTheory.FinDist

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exact uniform sampling of dyadic modular data

## Main definitions

* `bitsToResidue`: read a fixed number of independent MSB-first bits as a residue.
* `bitsToVector`, `bitsToMatrix`: apply that reader to disjoint coordinate blocks.

## Main results

The bijection and pushforward statements identify the actual uniform sampling laws.
Canonical encoding recovers every input bit when the modulus is exactly a power of two.
All nontrivial statements are admitted for the combined statement audit.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definition 4.2.3 (uniform matrix and secret in the LWE experiment).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010,
  Section 2.1 (binary random tapes).

This is a repository representation adaptation. Exact fair-bit sampling is asserted
only under `q = 2^width`; no rejection sampler or approximation for odd moduli is
implicit. Width zero, modulus one and empty dimensions are included. These finite
maps do not by themselves establish an efficient uniform parameter schedule.
-/

namespace TCSlib.Cryptography.Encoding.DyadicUniform

open TCSlib.InformationTheory
open TCSlib.Cryptography.NumberTheory (listToNat)

/-- Read the MSB-first word of `width` bits, then cast its value modulo `q`
[Pei16, Definition 4.2.3; PS10, Section 2.1, representation adaptation]. -/
def bitsToResidue {q : ℕ} [NeZero q] (width : ℕ)
    (r : Fin width → Bool) : ZMod q :=
  (listToNat (List.ofFn r) : ZMod q)

/-- The residue reader casts the natural value of the complete input word. -/
theorem bitsToResidue_eq {q : ℕ} [NeZero q] (width : ℕ)
    (r : Fin width → Bool) :
    bitsToResidue (q := q) width r = (listToNat (List.ofFn r) : ZMod q) := rfl

/-- At a power-of-two modulus, the fixed-width residue reader is a bijection.

**Proof sketch.** The numeral reader is less than `2^width`, so taking its
representative loses nothing. The existing fixed-width numeral round trips give
both inverses. At width zero both the seed and residue types have one element. -/
theorem bitsToResidue_bijective {q : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) : Function.Bijective (bitsToResidue (q := q) width) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro r s hrs
    apply List.ofFn_injective
    have recover (v : Fin width → Bool) :
        Candidates.natToList width (bitsToResidue (q := q) width v).val =
          List.ofFn v := by
      rw [bitsToResidue_eq]
      apply Candidates.natToList_val_natCast (List.length_ofFn v)
      simpa only [List.length_ofFn, hq] using
        Candidates.listToNat_lt_two_pow (List.ofFn v)
    exact (recover r).symm.trans
      ((congrArg (fun x : ZMod q => Candidates.natToList width x.val) hrs).trans
        (recover s))
  · simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ZMod.card, hq]

/-- A uniform block of bits induces the full uniform residue law at a dyadic modulus.

**Proof sketch.** Apply the preceding bijection to each singleton fibre of the
uniform pushforward, using `FinDist.map_apply` and `FinDist.uniform_apply`. -/
theorem bitsToResidue_uniform {q : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) :
    (FinDist.uniform (Fin width → Bool)).map (bitsToResidue (q := q) width) =
      FinDist.uniform (ZMod q) := by
  classical
  have hb := bitsToResidue_bijective (q := q) width hq
  apply FinDist.ext
  intro y
  rw [FinDist.map_apply, FinDist.uniform_apply, Finset.sum_filter]
  simp only [FinDist.uniform_apply, Fintype.card_of_bijective hb]
  calc
    (∑ x : Fin width → Bool,
        if bitsToResidue (q := q) width x = y then (Fintype.card (ZMod q) : ℝ)⁻¹ else 0) =
        ∑ z : ZMod q, if z = y then (Fintype.card (ZMod q) : ℝ)⁻¹ else 0 :=
      Fintype.sum_bijective _ hb _ _ (fun _ => rfl)
    _ = _ := by simp

/-- Re-encoding a residue sampled from one full-width block returns all original bits.

**Proof sketch.** The input word has length `width` and value below the modulus.
Read the residue representative and apply the public numeral reconstruction theorem. -/
theorem encode_bitsToResidue {q : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) (r : Fin width → Bool) :
    Candidates.natToList width (bitsToResidue (q := q) width r).val = List.ofFn r := by
  rw [bitsToResidue_eq]
  apply Candidates.natToList_val_natCast (List.length_ofFn r)
  simpa only [List.length_ofFn, hq] using
    Candidates.listToNat_lt_two_pow (List.ofFn r)

/-- Read independent full-width residue blocks as a modular vector
[Pei16, Definition 4.2.3, fair-bit specialization]. -/
def bitsToVector {q length : ℕ} [NeZero q] (width : ℕ)
    (r : Fin length → Fin width → Bool) : Fin length → ZMod q :=
  fun i => bitsToResidue width (r i)

/-- Coordinate `i` is obtained by reading exactly block `r i`. -/
theorem bitsToVector_apply {q length : ℕ} [NeZero q] (width : ℕ)
    (r : Fin length → Fin width → Bool) (i : Fin length) :
    bitsToVector (q := q) width r i = bitsToResidue width (r i) := rfl

/-- Disjoint dyadic residue blocks give a bijection onto the full vector space.

**Proof sketch.** Apply scalar injectivity and surjectivity coordinatewise;
finite function extensionality and choice assemble the inverses. -/
theorem bitsToVector_bijective {q length : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) :
    Function.Bijective (bitsToVector (q := q) (length := length) width) := by
  constructor
  · intro r s h
    funext i
    apply (bitsToResidue_bijective (q := q) width hq).1
    simpa only [bitsToVector_apply] using congrFun h i
  · intro v
    classical
    choose r hr using fun i : Fin length =>
      (bitsToResidue_bijective (q := q) width hq).2 (v i)
    refine ⟨r, ?_⟩
    funext i
    exact (bitsToVector_apply width r i).trans (hr i)

/-- Uniform independent bit blocks give the exact full uniform vector law.

**Proof sketch.** Count singleton fibres using `bitsToVector_bijective` and the
public pushforward equation. Independence is retained by the function-space seed. -/
theorem bitsToVector_uniform {q length : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) :
    (FinDist.uniform (Fin length → Fin width → Bool)).map
      (bitsToVector (q := q) width) = FinDist.uniform (Fin length → ZMod q) := by
  classical
  have hb := bitsToVector_bijective (q := q) (length := length) width hq
  apply FinDist.ext
  intro y
  rw [FinDist.map_apply, FinDist.uniform_apply, Finset.sum_filter]
  simp only [FinDist.uniform_apply, Fintype.card_of_bijective hb]
  calc
    (∑ x : Fin length → Fin width → Bool,
        if bitsToVector (q := q) width x = y then
          (Fintype.card (Fin length → ZMod q) : ℝ)⁻¹ else 0) =
        ∑ z : Fin length → ZMod q,
          if z = y then (Fintype.card (Fin length → ZMod q) : ℝ)⁻¹ else 0 :=
      Fintype.sum_bijective _ hb _ _ (fun _ => rfl)
    _ = _ := by simp

/-- Encoding a sampled vector concatenates the original bit blocks in coordinate order.

**Proof sketch.** Read `Modular.encodeVector_eq`, substitute the scalar reconstruction
theorem in each block, and retain the original increasing-coordinate order. -/
theorem encode_bitsToVector {q length : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) (r : Fin length → Fin width → Bool) :
    Modular.encodeVector width (bitsToVector (q := q) width r) =
      (List.ofFn fun i => List.ofFn (r i)).flatten := by
  simp only [Modular.encodeVector_eq, bitsToVector_apply, encode_bitsToResidue width hq]

/-- Read disjoint row-major bit blocks as a modular matrix
[Pei16, Definition 4.2.3, fair-bit specialization]. -/
def bitsToMatrix {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (r : Fin rows → Fin columns → Fin width → Bool) :
    Matrix (Fin rows) (Fin columns) (ZMod q) :=
  fun i => bitsToVector width (r i)

/-- Entry `(i,j)` is obtained by reading block `r i j`. -/
theorem bitsToMatrix_apply {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (r : Fin rows → Fin columns → Fin width → Bool)
    (i : Fin rows) (j : Fin columns) :
    bitsToMatrix (q := q) width r i j = bitsToResidue width (r i j) := rfl

/-- The row-major matrix reader is a bijection at an exact dyadic modulus.

**Proof sketch.** Apply vector bijectivity independently to each row. Empty rows
or columns give a singleton matrix space and require no positive-dimension premise. -/
theorem bitsToMatrix_bijective {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) :
    Function.Bijective (bitsToMatrix (q := q) (rows := rows) (columns := columns) width) := by
  constructor
  · intro r s h
    funext i
    apply (bitsToVector_bijective (q := q) (length := columns) width hq).1
    funext j
    simpa only [bitsToVector_apply, bitsToMatrix_apply] using congrFun (congrFun h i) j
  · intro A
    classical
    choose r hr using fun i : Fin rows =>
      (bitsToVector_bijective (q := q) (length := columns) width hq).2 (A i)
    refine ⟨r, ?_⟩
    funext i j
    exact (bitsToMatrix_apply width r i j).trans
      ((bitsToVector_apply width (r i) j).symm.trans (congrFun (hr i) j))

/-- Uniform matrix blocks induce exactly the full uniform modular matrix distribution.

**Proof sketch.** Count fibres of the matrix bijection using the existing finite
uniform pushforward equations. No entry or column is fixed to a special value. -/
theorem bitsToMatrix_uniform {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) :
    (FinDist.uniform (Fin rows → Fin columns → Fin width → Bool)).map
      (bitsToMatrix (q := q) width) =
        FinDist.uniform (Matrix (Fin rows) (Fin columns) (ZMod q)) := by
  classical
  have hb := bitsToMatrix_bijective (q := q) (rows := rows) (columns := columns) width hq
  apply FinDist.ext
  intro y
  rw [FinDist.map_apply, FinDist.uniform_apply, Finset.sum_filter]
  simp only [FinDist.uniform_apply, Fintype.card_of_bijective hb]
  calc
    (∑ x : Fin rows → Fin columns → Fin width → Bool,
        if bitsToMatrix (q := q) width x = y then
          (Fintype.card (Matrix (Fin rows) (Fin columns) (ZMod q)) : ℝ)⁻¹ else 0) =
        ∑ z : Matrix (Fin rows) (Fin columns) (ZMod q),
          if z = y then
            (Fintype.card (Matrix (Fin rows) (Fin columns) (ZMod q)) : ℝ)⁻¹ else 0 :=
      Fintype.sum_bijective _ hb _ _ (fun _ => rfl)
    _ = _ := by simp

/-- Canonical matrix encoding recovers every row-major input bit block.

**Proof sketch.** Read `Modular.encodeMatrix_eq` and apply vector reconstruction
to each row. The result uses the same row-major ordering as the LWE encoding. -/
theorem encode_bitsToMatrix {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) (r : Fin rows → Fin columns → Fin width → Bool) :
    Modular.encodeMatrix width (bitsToMatrix (q := q) width r) =
      (List.ofFn fun i => (List.ofFn fun j => List.ofFn (r i j)).flatten).flatten := by
  simp only [Modular.encodeMatrix_eq, Modular.encodeVector_eq, bitsToMatrix_apply,
    encode_bitsToResidue width hq]

end TCSlib.Cryptography.Encoding.DyadicUniform
