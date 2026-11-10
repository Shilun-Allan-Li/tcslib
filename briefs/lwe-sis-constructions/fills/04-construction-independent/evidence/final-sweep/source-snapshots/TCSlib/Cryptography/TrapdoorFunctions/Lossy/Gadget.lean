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
strict bounded integer perturbation. Gadget multiplication reads the original binary
blocks. These are statement-phase obligations, not completed lattice or security proofs.

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
  sorry

/-- The exact dyadic encoder is additive, with wraparound included.

**Proof sketch.** Represent both small residues by integers and apply `encode_intCast`.
Distribute the scale multiplication and use the public cast equations. -/
theorem encode_add (b a : ℕ) (x y : ZMod (2 ^ b)) :
    encode b a (x + y) = encode b a x + encode b a y := by
  sorry

/-- A perturbation of magnitude strictly below half a scale step is decoded exactly
[PW10, Section 6.3, deterministic bounded-noise adaptation].

**Proof sketch.** Write the representative of the encoded point plus error as a
multiple of the scale plus that error, up to a multiple of the full modulus.
The strict bound places the half-shifted error in `[0,2^a)`. Natural division gives
the original small representative modulo `2^b`, including wraparound and either sign. -/
theorem decode_encode_add (b a : ℕ) (ha : 0 < a) (m : ZMod (2 ^ b)) (e : ℤ)
    (he : 2 * e.natAbs < 2 ^ a) :
    decode b a (encode b a m + (e : ZMod (2 ^ (b + a)))) = m := by
  sorry

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

**Proof sketch.** Apply the public `Randomized.blocksEquiv_apply` and the proposed
owner-side `Randomized.blockVal_eq` reader, then the public binary-value equations.
Match the product index with `finProdFinEquiv`. The shared reader is recorded but
unapplied; this proof route waits for its coordination and landing before filling. -/
theorem digits_val (b w : ℕ) (x : Fin (w * b) → Bool) (j : Fin w) :
    (digits b w x j : ℕ) =
      ∑ k : Fin b, (x (finProdFinEquiv (j, k))).toNat * 2 ^ (k : ℕ) := by
  sorry

/-- The gadget transpose maps the binary input to its integer block digits.

**Proof sketch.** Split the finite product index into block and position. The
off-block entries vanish and the surviving positional sum is `digits_val`. -/
theorem gadget_mulVec (b w : ℕ) (x : Fin (w * b) → Bool) (j : Fin w) :
    (gadget b w).transpose.mulVec (fun i => ((x i).toNat : ℤ)) j =
      ((digits b w x j : ℕ) : ℤ) := by
  sorry

/-- The full digit vector uniquely determines every binary input coordinate.

**Proof sketch.** Read `digits_eq` and apply injectivity of the existing block equivalence. -/
theorem digits_injective (b w : ℕ) : Function.Injective (digits b w) := by
  sorry

end TCSlib.Cryptography.TrapdoorFunctions.Lossy
