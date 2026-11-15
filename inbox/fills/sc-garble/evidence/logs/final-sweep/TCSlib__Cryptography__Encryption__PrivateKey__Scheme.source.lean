/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Adversary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Private-key encryption schemes

## Main definitions

`TCSlib.Cryptography.PrivateKeyScheme` packages uniform polynomial-time key generation,
encryption and decryption for `n`-bit messages [PS10, Definition 24.7].

## Main results

The `correct` field requires decryption to recover the message for every choice of
key-generation, encryption and decryption coins.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1.3, Definition 24.7.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Efficient private-key encryption [PS10, Definition 24.7] -/

/-- An **efficient private-key encryption scheme** [PS10, Definition 24.7]: three PPTs
(`Complexity.NUPPT`s with empty advice) — `Gen(1^n)` samples a key `k`, `Enc_k(m)` encrypts
an `n`-bit message, `Dec_k(c)` decrypts a ciphertext into an `n`-bit message or `⊥` — such
that for every `n`, every `m ∈ {0,1}^n` and every choice of coins,
`Dec_k(Enc_k(m)) = m` where `k ← Gen(1^n)` (clause (4), probability one).
`Enc` and `Dec` are activated at parameter `n` on the pair `⟨k, m⟩` resp. `⟨k, c⟩`; the
output of `Dec` is decoded as an `n`-bit string by `decodeFin` (`none` is `⊥`).

**Deviation:** `PrivateKeyScheme`: messages at parameter `n` are the `n`-bit strings, keys
and ciphertexts arbitrary strings; `Enc` and `Dec` are activated at parameter `n` on
`⟨1^n, ⟨k, ·⟩⟩`; correctness holds for every coin string (the probability-one reading of
[PS10, Definition 24.6], `Complexity.NUPPT.computes_iff_uprob`); `Dec`'s `⊥` is any output
that does not decode to an `n`-bit string. -/
structure PrivateKeyScheme where
  /-- The key generator `Gen(1^n)`. -/
  gen : NUPPT
  /-- The encryption algorithm `Enc_k(m)`, activated on `⟨k, m⟩`. -/
  enc : NUPPT
  /-- The decryption algorithm `Dec_k(c)`, activated on `⟨k, c⟩`. -/
  dec : NUPPT
  /-- `Gen` is a PPT (no advice). -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT (no advice). -/
  enc_uniform : enc.Uniform
  /-- `Dec` is a PPT (no advice). -/
  dec_uniform : dec.Uniform
  /-- Perfect correctness [PS10, Definition 24.7 (4)], for every coin string. -/
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n) (rd : dec.Coins n),
    decodeFin n (dec.runAt n (pairEncode (gen.runAt n [] rg)
      (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) re)) rd) = some m

end TCSlib.Cryptography
