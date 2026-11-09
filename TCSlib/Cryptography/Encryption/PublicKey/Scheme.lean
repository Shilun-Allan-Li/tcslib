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
# Public-key encryption schemes

## Main definitions

* `TCSlib.Cryptography.PublicKeyScheme` is the scheme interface for `n`-bit messages.
* `TCSlib.Cryptography.BitPublicKeyScheme` is the interface for a single-bit message.

## Main results

Each `correct` field requires decryption to recover the message for every choice of
key-generation and encryption coins.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 102.1 and Algorithm 104.3.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-- A **public-key encryption scheme** [PS10, Definition 102.1]: a PPT key generator
`Gen(1^n) = ⟨pk, sk⟩`, a PPT encryptor `Enc_pk(m)` for `m ∈ {0,1}^n` (activated on `⟨pk, m⟩`),
a deterministic polynomial-time decryptor `Dec_sk(c)` (applied to `⟨sk, c⟩`, output decoded as an
`n`-bit string, `⊥` = any other output), with perfect correctness (clause (5)) for every coin
string.

**Deviation:** `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the
canonical message. -/
structure PublicKeyScheme where
  /-- The key generator `Gen(1^n) = ⟨pk, sk⟩`. -/
  gen : NUPPT
  /-- The encryptor `Enc_pk(m)`, activated on `⟨pk, m⟩`. -/
  enc : NUPPT
  /-- The deterministic decryptor on `⟨sk, c⟩`. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec
  /-- Perfect correctness [PS10, Definition 102.1 (5)]. -/
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin n (dec (pairEncode (pairSndD (gen.runAt n [] rg))
      (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m

/-- A **single-bit public-key encryption scheme**: [PS10, Definition 102.1] with message space
`{0,1}` (the message `b` is the string `[b]`), as used in [PS10, p. 103 and Algorithm 104.3]. The
components and the conventions are those of `PublicKeyScheme`; correctness is `Dec_sk(Enc_pk(b)) = [b]`
for every coin string. -/
structure BitPublicKeyScheme where
  /-- The key generator `Gen(1^n) = ⟨pk, sk⟩`. -/
  gen : NUPPT
  /-- The encryptor `Enc_pk(b)`, activated on `⟨pk, [b]⟩`. -/
  enc : NUPPT
  /-- The deterministic decryptor on `⟨sk, c⟩`. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec
  /-- Perfect correctness on both bits, for every coin string. -/
  correct : ∀ n (b : Bool) (rg : gen.Coins n) (re : enc.Coins n),
    dec (pairEncode (pairSndD (gen.runAt n [] rg))
      (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) [b]) re)) = [b]

end TCSlib.Cryptography
