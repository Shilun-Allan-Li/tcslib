/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Complexity.Randomized.RandomBits
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exact dyadic gadgets for cryptographic trapdoors

## Main definitions

* `encode`, `decode`: scale residues between exactly divisible dyadic moduli and round back.
* `gadget`, `digits`: binary block decomposition using the existing little-endian bit equivalence.

## Main results

Encoding respects integer casts and addition. Rounding recovers messages under a
strict bounded integer perturbation. The gadget transpose reads the positional
digits, and block packing makes the digit map injective.

## References

* [PW10] C. Peikert, B. Waters, *Lossy Trapdoor Functions and Their Applications*,
  author version 4 June 2010, Sections 6.2--6.3, printed pages 33--36.

This is a disclosed bounded-noise dyadic adaptation: the small modulus divides the
large one exactly, unlike an arbitrary-modulus rounded encoding. It establishes no
Gaussian transfer, worst-case reduction, or hardness for the chosen parameters.
The trapdoor consumer retains an ordinary secret matrix, not a short lattice basis.
Gadget digits are little-endian as in the existing `Randomized.blocksEquiv`; this
internal convention does not change the external MSB-first challenge encodings.
-/

namespace TCSlib.Cryptography.TrapdoorFunctions.Lossy

/-- Embed a residue modulo `2^b` into modulus `2^(b+a)` by multiplying its representative
by `2^a` [PW10, Section 6.3, exact-divisibility adaptation]. -/
def encode (b a : ℕ) (m : ZMod (2 ^ b)) : ZMod (2 ^ (b + a)) :=
  (2 ^ a : ZMod (2 ^ (b + a))) * (m.val : ZMod (2 ^ (b + a)))

/-- The complete encoding multiplies the small canonical representative by the scale. -/
theorem encode_eq (b a : ℕ) (m : ZMod (2 ^ b)) :
    encode b a m =
      (2 ^ a : ZMod (2 ^ (b + a))) * (m.val : ZMod (2 ^ (b + a))) := rfl

/-- Round a large-modulus representative to the nearest scale multiple and reduce the
quotient modulo `2^b` [PW10, Section 6.3, explicit dyadic convention]. -/
def decode (b a : ℕ) (z : ZMod (2 ^ (b + a))) : ZMod (2 ^ b) :=
  ((z.val + 2 ^ a / 2) / 2 ^ a : ℕ)

/-- The complete decoder adds a half-step, divides by the scale, then casts the quotient. -/
theorem decode_eq (b a : ℕ) (z : ZMod (2 ^ (b + a))) :
    decode b a z = (((z.val + 2 ^ a / 2) / 2 ^ a : ℕ) : ZMod (2 ^ b)) := rfl

/-- Encoding an integer cast is exactly multiplication of its large-modulus cast
by the scale; signed inputs are included [PW10, Section 6.3, dyadic refinement].

**Proof sketch.** The small representative differs from the integer by a multiple
of `2^b`. Multiplication by `2^a` makes that difference a multiple of the large modulus. -/
theorem encode_intCast (b a : ℕ) (z : ℤ) :
    encode b a (z : ZMod (2 ^ b)) =
      (2 ^ a : ZMod (2 ^ (b + a))) * (z : ZMod (2 ^ (b + a))) := by
  have hrep : (((z : ZMod (2 ^ b)).val : ℤ) : ZMod (2 ^ b)) =
      (z : ZMod (2 ^ b)) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hrep
  have hscaled : (↑(2 ^ (b + a) : ℕ) : ℤ) ∣
      (2 : ℤ) ^ a * z - (2 : ℤ) ^ a * ((z : ZMod (2 ^ b)).val : ℤ) := by
    refine ⟨t, ?_⟩
    rw [← mul_sub, ht]
    simp only [pow_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [encode_eq]
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] using
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr hscaled

/-- The exact dyadic encoder is additive, with wraparound included.

**Proof sketch.** Represent both small residues by integers and apply `encode_intCast`.
Distribute the scale multiplication and use the public cast equations. -/
theorem encode_add (b a : ℕ) (x y : ZMod (2 ^ b)) :
    encode b a (x + y) = encode b a x + encode b a y := by
  have hx : ((x.val : ℤ) : ZMod (2 ^ b)) = x := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hy : ((y.val : ℤ) : ZMod (2 ^ b)) = y := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← hx, ← hy, ← Int.cast_add, encode_intCast, encode_intCast, encode_intCast,
    Int.cast_add, mul_add]

/-- A perturbation of magnitude strictly below half a scale step is decoded exactly
[PW10, Section 6.3, deterministic bounded-noise adaptation].

**Proof sketch.** Write the representative of the encoded point plus error as a
multiple of the scale plus that error, up to a multiple of the full modulus.
The strict bound places the half-shifted error in `[0,2^a)`. Transport the natural
division to integer division and remove the multiple of `2^b` on casting back. -/
theorem decode_encode_add (b a : ℕ) (ha : 0 < a) (m : ZMod (2 ^ b)) (e : ℤ)
    (he : 2 * e.natAbs < 2 ^ a) :
    decode b a (encode b a m + (e : ZMod (2 ^ (b + a)))) = m := by
  let z := encode b a m + (e : ZMod (2 ^ (b + a)))
  have hz : z = (((2 : ℤ) ^ a * (m.val : ℤ) + e : ℤ) : ZMod (2 ^ (b + a))) := by
    dsimp only [z]
    rw [encode_eq]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast]
  have hrep : ((z.val : ℤ) : ZMod (2 ^ (b + a))) = z := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (hz.symm.trans hrep.symm)
  have hs : (2 : ℤ) ≤ 2 ^ a := by
    calc
      2 = (2 : ℤ) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ 2 ^ a := pow_le_pow_right₀ (by decide) ha
  have habs : (2 : ℤ) * |e| < (2 : ℤ) ^ a := by
    have hcast : (2 : ℤ) * (e.natAbs : ℤ) < (2 : ℤ) ^ a := by exact_mod_cast he
    simpa only [Int.natCast_natAbs] using hcast
  have hlo : 0 ≤ e + (2 : ℤ) ^ a / 2 := by
    have h := neg_abs_le e
    omega
  have hhi : e + (2 : ℤ) ^ a / 2 < (2 : ℤ) ^ a := by
    have h := le_abs_self e
    omega
  have hval : (z.val : ℤ) = (2 : ℤ) ^ a * (m.val : ℤ) + e +
      ((2 : ℤ) ^ b * (2 : ℤ) ^ a) * t := by
    have hmodulus : (↑(2 ^ (b + a) : ℕ) : ℤ) = (2 : ℤ) ^ b * (2 : ℤ) ^ a := by
      rw [pow_add (2 : ℕ) b a, Nat.cast_mul]
      push_cast
      rfl
    have hdiff : (z.val : ℤ) - ((2 : ℤ) ^ a * (m.val : ℤ) + e) =
        ((2 : ℤ) ^ b * (2 : ℤ) ^ a) * t :=
      ht.trans (congrArg (fun scale : ℤ => scale * t) hmodulus)
    omega
  have hshift : (z.val : ℤ) + (2 : ℤ) ^ a / 2 =
      (e + (2 : ℤ) ^ a / 2) + ((m.val : ℤ) + (2 : ℤ) ^ b * t) * (2 : ℤ) ^ a := by
    rw [hval]
    ring
  have hdiv : (((z.val + 2 ^ a / 2) / 2 ^ a : ℕ) : ℤ) =
      (m.val : ℤ) + (2 : ℤ) ^ b * t := by
    simp only [Int.natCast_ediv, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    rw [hshift, Int.add_mul_ediv_right _ _ (by omega : (2 : ℤ) ^ a ≠ 0),
      Int.ediv_eq_zero_of_lt hlo hhi, zero_add]
  have hmod : (↑((2 : ℤ) ^ b) : ZMod (2 ^ b)) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact dvd_refl _
  change decode b a z = m
  rw [decode_eq, ← Int.cast_natCast, hdiv]
  simp only [Int.cast_add, Int.cast_mul, hmod, zero_mul, add_zero, Int.cast_natCast,
    ZMod.natCast_zmod_val]

/-- Put the powers of two for each little-endian block in that block's column
[PW10, Section 6.3, transposed gadget convention]. -/
def gadget (b w : ℕ) : Matrix (Fin (w * b)) (Fin w) ℤ :=
  fun i j =>
    let jk : Fin w × Fin b := finProdFinEquiv.symm i
    if jk.1 = j then 2 ^ (jk.2 : ℕ) else 0

/-- The complete gadget entry is the block's positional power in its own column, else zero. -/
theorem gadget_eq (b w : ℕ) (i : Fin (w * b)) (j : Fin w) :
    gadget b w i j =
      let jk : Fin w × Fin b := finProdFinEquiv.symm i
      if jk.1 = j then 2 ^ (jk.2 : ℕ) else 0 := rfl

/-- Read each block of `b` binary input coordinates through the existing finite bit
equivalence [PW10, Section 6.3, explicit digit convention]. -/
def digits (b w : ℕ) (x : Fin (w * b) → Bool) : Fin w → Fin (2 ^ b) :=
  Randomized.blocksEquiv w b x

/-- The complete digit map is the existing little-endian block equivalence. -/
theorem digits_eq (b w : ℕ) (x : Fin (w * b) → Bool) :
    digits b w x = Randomized.blocksEquiv w b x := rfl

/-- Each digit equals its block's positional binary sum.

**Proof sketch.** Read the selected slice through the shared block equation.
Its length is exactly the block width. Evaluate its positional sum, then reindex
by that width. Reading each slice coordinate gives the corresponding row-major
input position. -/
theorem digits_val (b w : ℕ) (x : Fin (w * b) → Bool) (j : Fin w) :
    (digits b w x j : ℕ) =
      ∑ k : Fin b, (x (finProdFinEquiv (j, k))).toNat * 2 ^ (k : ℕ) := by
  rw [digits_eq, Randomized.blocksEquiv_apply, Randomized.blockVal_eq]
  let slice := ((List.ofFn x).drop (j.val * b)).take b
  have hcut : j.val * b + b ≤ w * b := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right b (Nat.succ_le_of_lt j.isLt)
  have hlength : slice.length = b := by
    dsimp only [slice]
    rw [List.length_take, List.length_drop, List.length_ofFn]
    omega
  have hvalue : Complexity.LogProg.bitsVal slice =
      ∑ k : Fin slice.length, (slice[k.val]'k.isLt).toNat * 2 ^ k.val := by
    have h := Randomized.bitsVal_ofFn (fun k : Fin slice.length => slice[k.val]'k.isLt)
    rwa [List.ofFn_getElem] at h
  change Complexity.LogProg.bitsVal slice = _
  rw [hvalue]
  refine Fintype.sum_equiv (finCongr hlength) _ _ fun k => ?_
  have hbit : slice[k.val]'k.isLt = x (finProdFinEquiv (j, finCongr hlength k)) := by
    dsimp only [slice]
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    apply congrArg x
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val, finCongr_apply_coe, Nat.add_comm, Nat.mul_comm]
  rw [hbit, finCongr_apply_coe]

/-- The gadget transpose maps the binary input to its integer block digits.

**Proof sketch.** Split the finite product index into block and position. The
off-block entries vanish and the surviving positional sum is `digits_val`. -/
theorem gadget_mulVec (b w : ℕ) (x : Fin (w * b) → Bool) (j : Fin w) :
    (gadget b w).transpose.mulVec (fun i => ((x i).toNat : ℤ)) j =
      ((digits b w x j : ℕ) : ℤ) := by
  classical
  change (∑ i, gadget b w i j * ((x i).toNat : ℤ)) = _
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [gadget_eq, Equiv.symm_apply_apply, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [digits_val, Nat.cast_sum]
  exact Finset.sum_congr rfl fun k _ => by
    push_cast
    ring

/-- The full digit vector uniquely determines every binary input coordinate.

**Proof sketch.** Read `digits_eq` and apply injectivity of the existing block equivalence. -/
theorem digits_injective (b w : ℕ) : Function.Injective (digits b w) := by
  intro x y h
  rw [digits_eq, digits_eq] at h
  exact (Randomized.blocksEquiv w b).injective h

end TCSlib.Cryptography.TrapdoorFunctions.Lossy
