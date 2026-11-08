/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.BitEncoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Regev public-key encryption: subset sums and correctness

## Main definitions

* `keygen`: publish the existing LWE sample and retain its one common secret.
* `encrypt`: sum the public samples selected by fresh binary coins, adding a bit codepoint.
* `decrypt`: subtract the secret product and use the existing nearest-codepoint decoder.

## Main results

The residual is the integer subset sum of the original errors plus the codepoint.
The worst-case support bound gives every-coin correctness under an explicit strict
separation condition. Nontrivial proofs are left for the combined statement audit.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Section 5.2.1 (Regev's LWE cryptosystem).
* [Wu24] D. Wu, CS395T *Topics in Cryptography*, Spring 2024 notes, Lecture 21.

Rows are samples, transposing the presentation in Pei16. The bit codepoint is
`floor(q/2)` and ties decode false. The explicit strict condition below is stronger
than a non-strict quarter-modulus shorthand. This is primal Regev PKE; no lattice
trapdoor, search-LWE reduction, efficient machine or existing primitive bridge is
introduced by these mathematical maps.
-/

namespace TCSlib.Cryptography.Encryption.PublicKey.Regev

open LWE (Parameters Noise)

/-- Generate an LWE public key and retain its single common secret
[Pei16, Section 5.2.1; Wu24, Lecture 21]. -/
def keygen (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) × (Fin P.dimension → ZMod P.modulus) :=
  (LWE.sample P χ r, r.2.1)

/-- The public-key component is exactly the existing common-secret LWE sample. -/
theorem keygen_fst (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    (keygen P χ r).1 = LWE.sample P χ r := rfl

/-- The retained secret is the seed's one full uniform secret vector. -/
theorem keygen_snd (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    (keygen P χ r).2 = r.2.1 := rfl

/-- Encrypt one bit by a binary subset sum of public samples plus its bit codepoint
[Pei16, Section 5.2.1; Wu24, Lecture 21]. -/
def encrypt (P : Parameters)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) (μ : Bool) (r : Fin P.samples → Bool) :
    (Fin P.dimension → ZMod P.modulus) × ZMod P.modulus :=
  (pk.1.transpose.mulVec (fun i => ((r i).toNat : ZMod P.modulus)),
    (∑ i, pk.2 i * ((r i).toNat : ZMod P.modulus)) + LWE.BitEncoding.codepoint P μ)

/-- The vector component is the transpose matrix times the binary subset vector. -/
theorem encrypt_fst (P : Parameters)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) (μ : Bool) (r : Fin P.samples → Bool) :
    (encrypt P pk μ r).1 =
      pk.1.transpose.mulVec (fun i => ((r i).toNat : ZMod P.modulus)) := rfl

/-- The scalar component is the selected public-value sum plus the message codepoint. -/
theorem encrypt_snd (P : Parameters)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) (μ : Bool) (r : Fin P.samples → Bool) :
    (encrypt P pk μ r).2 =
      (∑ i, pk.2 i * ((r i).toNat : ZMod P.modulus)) + LWE.BitEncoding.codepoint P μ := rfl

/-- Decrypt by subtracting the secret inner product and decoding the resulting residue
[Pei16, Section 5.2.1, specified nearest-codepoint convention]. -/
def decrypt (P : Parameters) (s : Fin P.dimension → ZMod P.modulus)
    (c : (Fin P.dimension → ZMod P.modulus) × ZMod P.modulus) : Bool :=
  LWE.BitEncoding.decode P (c.2 - ∑ j, s j * c.1 j)

/-- Decryption reads exactly the scalar residual after the secret product is removed. -/
theorem decrypt_eq (P : Parameters) (s : Fin P.dimension → ZMod P.modulus)
    (c : (Fin P.dimension → ZMod P.modulus) × ZMod P.modulus) :
    decrypt P s c = LWE.BitEncoding.decode P (c.2 - ∑ j, s j * c.1 j) := rfl

/-- The decryption residual equals the message codepoint plus the original integer
subset-error sum reduced modulo `q` [Pei16, Section 5.2.1].

**Proof sketch.** Read both encryption projections and `LWE.noisyValues_apply`.
Distribute the selected-sample sum, swap the finite sums in the matrix-secret term,
and cancel that term against the secret product. Integer-cast add/multiply equations
identify the remaining sum without first reducing the errors' signs or magnitudes. -/
theorem encrypt_residual (P : Parameters)
    (A : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus))
    (s : Fin P.dimension → ZMod P.modulus) (e : Fin P.samples → ℤ)
    (μ : Bool) (r : Fin P.samples → Bool) :
    (encrypt P (A, LWE.noisyValues P A s e) μ r).2 -
      ∑ j, s j * (encrypt P (A, LWE.noisyValues P A s e) μ r).1 j =
    LWE.BitEncoding.codepoint P μ +
      ((∑ i, e i * ((r i).toNat : ℤ) : ℤ) : ZMod P.modulus) := by
  sorry

/-- Any binary subset of errors bounded by `B` has absolute sum at most `m*B`
[Pei16, Section 5.2.1, worst-case bounded-support specialization].

**Proof sketch.** Apply the integer triangle inequality. A selected coordinate has
absolute value at most `B`, and an unselected coordinate is zero; sum over all rows. -/
theorem subsetError_bound (P : Parameters) (e : Fin P.samples → ℤ)
    (r : Fin P.samples → Bool) (B : ℕ) (he : ∀ i, (e i).natAbs ≤ B) :
    (∑ i, e i * ((r i).toNat : ℤ)).natAbs ≤ P.samples * B := by
  sorry

/-- Bounded errors give correctness for every public matrix, secret, bit and subset
coin vector when `2*(m*B) < floor(q/2)` [Pei16, Section 5.2.1, strict refinement].

**Proof sketch.** Substitute `encrypt_residual`, bound the integer subset sum by
`subsetError_bound`, and apply the existing `decode_codepoint_add` theorem. -/
theorem decrypt_encrypt (P : Parameters)
    (A : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus))
    (s : Fin P.dimension → ZMod P.modulus) (e : Fin P.samples → ℤ)
    (μ : Bool) (r : Fin P.samples → Bool) (B : ℕ)
    (he : ∀ i, (e i).natAbs ≤ B) (hsep : 2 * (P.samples * B) < P.modulus / 2) :
    decrypt P s (encrypt P (A, LWE.noisyValues P A s e) μ r) = μ := by
  sorry

/-- Bounded finite-seed noise gives every-keygen-coin and every-encryption-coin
correctness for Regev PKE [Pei16, Section 5.2.1, finite-law specialization].

**Proof sketch.** Read the keygen projections and LWE sampler equation. The noise
support predicate bounds each original row error, so apply `decrypt_encrypt`. -/
theorem decrypt_keygen_encrypt (P : Parameters) (χ : Noise)
    (rg : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins)))
    (μ : Bool) (r : Fin P.samples → Bool) (B : ℕ)
    (hχ : χ.Bounded B) (hsep : 2 * (P.samples * B) < P.modulus / 2) :
    decrypt P (keygen P χ rg).2 (encrypt P (keygen P χ rg).1 μ r) = μ := by
  sorry

end TCSlib.Cryptography.Encryption.PublicKey.Regev
