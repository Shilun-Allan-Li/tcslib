/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.BitEncoding
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Direct Regev symmetric encryption: mathematical algorithms

## Main definitions

* `shift`: add the message's bit codepoints to an LWE challenge's value vector.
* `encrypt`: one fresh LWE row per message bit under a common secret.
* `decrypt`: subtract the matrix-secret product and decode each residual bit.

## Main results

`decrypt_encrypt` and its finite-noise corollary prove every-coin correctness under
an explicit bounded-error and codepoint-separation condition. Machine construction
and the existing primitive-security bridge remain separate obligations.

## References

* [Wu24] D. Wu, CS395T *Topics in Cryptography*, Spring 2024 lecture notes,
  compilation last updated 30 April 2024, Definition 20.5 and Lecture 21.

**Deviation.** Rows are samples, as in the existing LWE owner. The message length is
the number of rows; each row encrypts one bit under the same full uniform secret.
The later `PrivateKeyScheme` bridge uses exactly `κ` rows at parameter `κ`.
Decoding uses the explicit nearest-codepoint convention in `LWE.BitEncoding`.
This is direct noisy-inner-product encryption. No PRF construction, short lattice
basis, search-LWE reduction or Gaussian preimage sampler is used.
-/

namespace TCSlib.Cryptography.Encryption.Symmetric.Regev

open LWE (Parameters Noise)

/-- Add each plaintext bit's codepoint to the corresponding value of a matrix/value
challenge, retaining the matrix [Wu24, Definition 20.5, batched formulation]. -/
def shift (P : Parameters) (μ : Fin P.samples → Bool)
    (c : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) :
    Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus) :=
  (c.1, c.2 + fun i => LWE.BitEncoding.codepoint P (μ i))

attribute [simps (config := { isSimp := false }) fst snd] shift

/-- Encrypt all message bits using the matrix `A`, one common secret `s`, and the
coordinate errors `e`, then add their codepoints [Wu24, Definition 20.5]. The inputs
are the mathematical coins; the experiment chooses them with their specified laws. -/
def encrypt (P : Parameters) (s : Fin P.dimension → ZMod P.modulus)
    (A : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus))
    (e : Fin P.samples → ℤ) (μ : Fin P.samples → Bool) :
    Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus) :=
  shift P μ (A, LWE.noisyValues P A s e)

attribute [simps (config := { isSimp := false }) fst snd] encrypt

/-- Decrypt by subtracting `A s` and decoding each resulting coordinate to its nearer
bit codepoint [Wu24, Definition 20.5, specified nearest-codepoint convention]. -/
def decrypt (P : Parameters) (s : Fin P.dimension → ZMod P.modulus)
    (c : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) : Fin P.samples → Bool :=
  fun i => LWE.BitEncoding.decode P (c.2 i - (c.1.mulVec s) i)

/-- Coordinate `i` is obtained by decoding `c.2 i - (c.1.mulVec s) i`. -/
theorem decrypt_apply (P : Parameters) (s : Fin P.dimension → ZMod P.modulus)
    (c : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) (i : Fin P.samples) :
    decrypt P s c i = LWE.BitEncoding.decode P (c.2 i - (c.1.mulVec s) i) := rfl

/-- Every encrypted bit decrypts correctly when all coordinate errors have absolute
value at most `B` and `2 * B < floor(q/2)` [Wu24, Definition 20.5 and Lecture 21,
bounded-error refinement].

**Proof sketch.** Read the encryption projections and `LWE.noisyValues_apply`.
Subtract the matrix-secret product, leaving the bit codepoint plus that row's
integer error. Apply `LWE.BitEncoding.decode_codepoint_add` at each coordinate.
Function extensionality also handles the empty message. -/
theorem decrypt_encrypt (P : Parameters) (s : Fin P.dimension → ZMod P.modulus)
    (A : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus))
    (e : Fin P.samples → ℤ) (μ : Fin P.samples → Bool) (B : ℕ)
    (he : ∀ i, (e i).natAbs ≤ B) (hsep : 2 * B < P.modulus / 2) :
    decrypt P s (encrypt P s A e μ) = μ := by
  funext i
  rw [decrypt_apply, encrypt_snd, encrypt_fst, LWE.noisyValues_apply]
  change LWE.BitEncoding.decode P
    (((∑ j, A i j * s j) + (e i : ZMod P.modulus)) +
      LWE.BitEncoding.codepoint P (μ i) - (∑ j, A i j * s j)) = μ i
  rw [add_assoc, add_sub_cancel_left, add_comm]
  exact LWE.BitEncoding.decode_codepoint_add P B (μ i) (e i) (he i) hsep

/-- Bounded finite-seed scalar noise gives perfect decryption for every matrix,
secret, message and collection of row seeds [Wu24, Definition 20.5, finite-noise
specialization]. This asserts no sampler efficiency or Gaussian tail transfer.

**Proof sketch.** Read `Noise.bounded_iff` to bound every sampled row error, then
apply `decrypt_encrypt`. The assertion holds for every seed, not merely on average. -/
theorem decrypt_encrypt_noise (P : Parameters) (χ : Noise)
    (s : Fin P.dimension → ZMod P.modulus)
    (A : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus))
    (η : Fin P.samples → χ.Coins) (μ : Fin P.samples → Bool) (B : ℕ)
    (hnoise : χ.Bounded B) (hsep : 2 * B < P.modulus / 2) :
    decrypt P s (encrypt P s A (fun i => χ.sample (η i)) μ) = μ := by
  exact decrypt_encrypt P s A (fun i => χ.sample (η i)) μ B
    (fun i => (Noise.bounded_iff χ B).mp hnoise (η i)) hsep

end TCSlib.Cryptography.Encryption.Symmetric.Regev
