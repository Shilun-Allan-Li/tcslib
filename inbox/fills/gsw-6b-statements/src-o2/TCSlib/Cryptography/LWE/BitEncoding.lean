/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Basic
import Mathlib.Data.ZMod.ValMinAbs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bit codepoints and bounded-error decoding for Regev encryption

## Main definitions

* `BitEncoding.codepoint`: zero for false and `floor(q/2)` for true.
* `BitEncoding.distance`: circular distance using Mathlib's minimal integer lift.
* `BitEncoding.decode`: choose the nearer codepoint, breaking ties toward false.
* `BitEncoding.decodeLo`, `BitEncoding.decodeHi`: the ends of the decoding interval.

## Main results

The distance lemmas and `decode_codepoint_add` are proved below.
`decode_iff_mem_Ico` reads decoding as the interval test
`decodeLo P ≤ v.val < decodeHi P`.
The last theorem gives perfect decoding under the strict separation condition
`2 * B < q / 2`, with natural-number division.

## References

* [Wu24] D. Wu, CS395T *Topics in Cryptography*, Spring 2024 lecture notes,
  compilation last updated 30 April 2024, Definition 20.5 and Lecture 21.

**Deviation.** Nearest-codepoint decoding replaces the notes' informal rounding
notation. The strict separation condition covers arbitrary moduli, both error signs
and all finite parameters. The decoder is total, with an explicit tie rule. No exact
Gaussian sampling, tail bound or machine implementation is asserted.
-/

namespace TCSlib.Cryptography.LWE.BitEncoding

/-- The codepoint for a bit is zero or `floor(q/2)` modulo `q`
[Wu24, Definition 20.5]. -/
def codepoint (P : Parameters) (b : Bool) : ZMod P.modulus :=
  if b then ((P.modulus / 2 : ℕ) : ZMod P.modulus) else 0

/-- `codepoint P b` is `q/2` cast to residues when `b` is true and zero otherwise. -/
theorem codepoint_eq (P : Parameters) (b : Bool) :
    codepoint P b = if b then ((P.modulus / 2 : ℕ) : ZMod P.modulus) else 0 := rfl

/-- Circular distance is the natural absolute value of Mathlib's minimal integer
representative of `x - y`. This is technical decoding infrastructure. -/
def distance (P : Parameters) (x y : ZMod P.modulus) : ℕ :=
  (x - y).valMinAbs.natAbs

/-- The circular distance is `(x - y).valMinAbs.natAbs`. -/
theorem distance_eq (P : Parameters) (x y : ZMod P.modulus) :
    distance P x y = (x - y).valMinAbs.natAbs := rfl

/-- Circular distance is symmetric.

**Proof sketch.** Rewrite `y - x` as the negative of `x - y` and use the public
`ZMod.natAbs_valMinAbs_neg` lemma. -/
theorem distance_symm (P : Parameters) (x y : ZMod P.modulus) :
    distance P x y = distance P y x := by
  rw [distance_eq, distance_eq, ← neg_sub x y, ZMod.natAbs_valMinAbs_neg]

/-- Circular distance satisfies the triangle inequality.

**Proof sketch.** Write `x - z = (x - y) + (y - z)`. Apply
`ZMod.natAbs_valMinAbs_add_le`, then the integer absolute-value triangle inequality. -/
theorem distance_triangle (P : Parameters) (x y z : ZMod P.modulus) :
    distance P x z ≤ distance P x y + distance P y z := by
  rw [distance_eq, distance_eq, distance_eq, ← sub_add_sub_cancel x y z]
  exact (ZMod.natAbs_valMinAbs_add_le (x - y) (y - z)).trans
    (Int.natAbs_add_le _ _)

/-- Adding the same residue to both arguments preserves circular distance.

**Proof sketch.** Cancel the common translation in the difference and read `distance_eq`. -/
theorem distance_add_right (P : Parameters) (x y a : ZMod P.modulus) :
    distance P (x + a) (y + a) = distance P x y := by
  rw [distance_eq, distance_eq, add_sub_add_right_eq_sub]

/-- The two bit codepoints have circular distance `floor(q/2)`
[Wu24, Definition 20.5, exact separation].

**Proof sketch.** Use `ZMod.valMinAbs_natCast_of_le_half` for `q/2` and
`ZMod.natAbs_valMinAbs_neg` if the subtraction has the opposite sign. -/
theorem distance_codepoints (P : Parameters) :
    distance P (codepoint P false) (codepoint P true) = P.modulus / 2 := by
  rw [codepoint_eq, codepoint_eq]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [distance_eq, zero_sub, ZMod.natAbs_valMinAbs_neg,
    ZMod.valMinAbs_natCast_of_le_half (le_refl _), Int.natAbs_natCast]

/-- Reducing an integer error modulo the modulus cannot increase its distance
from zero beyond its original natural absolute value.

**Proof sketch.** Use `ZMod.coe_valMinAbs`, `ZMod.natAbs_valMinAbs_le` and
`ZMod.natAbs_min_of_le_div_two` to compare the minimal lift with the given integer. -/
theorem distance_intCast_zero_le (P : Parameters) (e : ℤ) :
    distance P (e : ZMod P.modulus) 0 ≤ e.natAbs := by
  rw [distance_eq, sub_zero]
  exact ZMod.natAbs_min_of_le_div_two P.modulus _ e
    (ZMod.coe_valMinAbs _) (ZMod.natAbs_valMinAbs_le _)

/-- Decode to true precisely when the true codepoint is strictly nearer;
equidistant inputs decode to false [Wu24, Definition 20.5, specified tie convention]. -/
def decode (P : Parameters) (x : ZMod P.modulus) : Bool :=
  decide (distance P x (codepoint P true) < distance P x (codepoint P false))

/-- Decoding compares the two circular distances, with a strict inequality for true. -/
theorem decode_eq (P : Parameters) (x : ZMod P.modulus) :
    decode P x =
      decide (distance P x (codepoint P true) < distance P x (codepoint P false)) := rfl

/-- The lower end of the decoding interval: `decodeLo P = ⌊⌊q/2⌋/2⌋ + 1`, the least
representative that decodes to true. Glue for the file's `decode`. -/
def decodeLo (P : Parameters) : ℕ :=
  P.modulus / 2 / 2 + 1

/-- `decodeLo P` is `P.modulus / 2 / 2 + 1`. -/
theorem decodeLo_eq (P : Parameters) : decodeLo P = P.modulus / 2 / 2 + 1 := rfl

/-- The upper end, exclusive, of the decoding interval: `decodeHi P = ⌊(q + ⌊q/2⌋ + 1)/2⌋`,
one more than the greatest representative that decodes to true. Glue for the file's
`decode`. -/
def decodeHi (P : Parameters) : ℕ :=
  (P.modulus + P.modulus / 2 + 1) / 2

/-- `decodeHi P` is `(P.modulus + P.modulus / 2 + 1) / 2`. -/
theorem decodeHi_eq (P : Parameters) : decodeHi P = (P.modulus + P.modulus / 2 + 1) / 2 := rfl

/-- **Decoding is an interval test**: a residue decodes to true exactly when its canonical
representative lies in `[decodeLo P, decodeHi P)`,
`decode P v = true ↔ decodeLo P ≤ v.val ∧ v.val < decodeHi P`. With `h = ⌊q/2⌋` the interval
is `[⌊h/2⌋ + 1, ⌊(q + h + 1)/2⌋)`. Glue for the file's `decode`, consumed by the GSW
decryption formula as an interval of the modular subset sum.

**Proof sketch.** Write `v` for the representative `v.val < q` and `h = ⌊q/2⌋ < q`. By
Mathlib's `ZMod.valMinAbs_natAbs_eq_min`, the natural absolute value of the minimal lift of a
residue `y` is `min y.val (q − y.val)`; this gives both distances through `distance_eq`.
The distance to the false codepoint (`codepoint_eq`) reads `v`. For the true codepoint `h`,
the representative of `v − h` is `v − h` when `h ≤ v` (`ZMod.val_sub`) and `v + q − h`
otherwise (the difference is the cast of `v + q − h`, by `ZMod.natCast_self` and
`ZMod.natCast_zmod_val`, below `q`). `decode_eq` compares the two distances strictly; after
the case split every case is linear arithmetic with `min` and divisions by `2`, which `omega`
closes against `decodeLo_eq` and `decodeHi_eq`. -/
theorem decode_iff_mem_Ico (P : Parameters) (v : ZMod P.modulus) :
    decode P v = true ↔ decodeLo P ≤ v.val ∧ v.val < decodeHi P := by
  have hq := P.modulus_ge_two
  have hv := ZMod.val_lt v
  -- Step 1: the representative of `v − ⌊q/2⌋`.
  have hh : P.modulus / 2 < P.modulus := by omega
  have hsub : (v - ((P.modulus / 2 : ℕ) : ZMod P.modulus)).val =
      if P.modulus / 2 ≤ v.val then v.val - P.modulus / 2
      else v.val + P.modulus - P.modulus / 2 := by
    split_ifs with hle
    · rw [ZMod.val_sub (by rwa [ZMod.val_natCast_of_lt hh]), ZMod.val_natCast_of_lt hh]
    · have hcast : v - ((P.modulus / 2 : ℕ) : ZMod P.modulus) =
          ((v.val + P.modulus - P.modulus / 2 : ℕ) : ZMod P.modulus) := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, ZMod.natCast_zmod_val,
          add_zero]
      rw [hcast, ZMod.val_natCast_of_lt (by omega)]
  -- Step 2: both distances as `min` of a representative and its complement
  -- (`ZMod.valMinAbs_natAbs_eq_min`); linear arithmetic in every case.
  rw [decode_eq, decide_eq_true_iff, distance_eq, distance_eq, codepoint_eq, codepoint_eq]
  simp only [if_true, Bool.false_eq_true, if_false, sub_zero]
  rw [ZMod.valMinAbs_natAbs_eq_min, ZMod.valMinAbs_natAbs_eq_min, hsub, decodeLo_eq, decodeHi_eq]
  split_ifs <;> omega

/-- An error of absolute value at most `B` preserves the encoded bit whenever
`2 * B < floor(q/2)` [Wu24, Definition 20.5 and Lecture 21, bounded-error refinement].

**Proof sketch.** Translation invariance and the integer-error bound put the received
residue within `B` of its intended codepoint. The triangle inequality and exact
codepoint separation put its distance to the other codepoint above `B`. The intended
codepoint is uniquely nearer, so the tie rule is immaterial for valid encryptions. -/
theorem decode_codepoint_add (P : Parameters) (B : ℕ) (b : Bool) (e : ℤ)
    (he : e.natAbs ≤ B) (hsep : 2 * B < P.modulus / 2) :
    decode P (codepoint P b + (e : ZMod P.modulus)) = b := by
  have herr : distance P (codepoint P b + (e : ZMod P.modulus)) (codepoint P b) ≤ B := by
    calc
      _ = distance P (e : ZMod P.modulus) 0 := by
        simpa only [zero_add, add_comm] using
          distance_add_right P (e : ZMod P.modulus) 0 (codepoint P b)
      _ ≤ e.natAbs := distance_intCast_zero_le P e
      _ ≤ B := he
  have htri := distance_triangle P (codepoint P false)
    (codepoint P b + (e : ZMod P.modulus)) (codepoint P true)
  rw [distance_codepoints, distance_symm P (codepoint P false)] at htri
  cases b
  · rw [decode_eq]
    exact decide_eq_false (by omega)
  · rw [decode_eq]
    exact decide_eq_true (by omega)

end TCSlib.Cryptography.LWE.BitEncoding
