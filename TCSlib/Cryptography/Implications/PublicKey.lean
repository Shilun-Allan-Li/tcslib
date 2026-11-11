/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA
import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor
import TCSlib.Cryptography.Candidates.RSA
import TCSlib.Cryptography.Candidates.Rabin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Implications: public-key encryption

Catalog of end-to-end results of the form "these hardness assumptions give a public-key encryption
scheme with this security". Each entry states its full assumption set and proves the conclusion by a
short composition of published results. The endpoint here is **adaptive multi-message IND-CPA with
`n`-bit messages**:

`∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa`.

`FixedLengthPKScheme` packages uniform polynomial-time key generation and encryption,
polynomial-time decryption, fixed-length ciphertexts and perfect correctness. `msgLen = .var`
makes the message space `{0,1}^n`, so the existential cannot be met by an empty-message scheme.
`AdaptiveINDSecure .cpa` is the left-or-right game of [PS10, Definition 171.5] with one public
key, one hidden bit and a polynomial number of adaptively chosen challenges.

## Main results

* `Implications.PublicKey.exists_adaptiveCPA_of_rsa`: from `ArithmeticFP` and `RSAAssumption`.
* `Implications.PublicKey.exists_adaptiveCPA_of_factoring`: from `ArithmeticFP`, `BlumDensity` and
  `FactoringAssumption`.

## The route

Both entries take the same steps:
1. A one-way trapdoor permutation collection (`rsaTrapdoor_oneWay`, `rabinBlumTrapdoor_oneWay`).
2. It is run at parameter `n + 2` (RSA) or `n + 3` (Rabin)
   (`TrapdoorCollection.shiftParameter_oneWay`), so that its encoding width is exactly the
   polynomial `2(n + 2)` or `2(n + 3)`
   (`rsaTrapdoor_shiftParameter_encD_length`, `rabinBlumTrapdoor_shiftParameter_encD_length`).
3. The Goldreich–Levin padded collection then gives a secure single-bit scheme of Algorithm 104.3
   (`TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`) [PS10, Theorems 87.3 and 104.4].
4. The padded bitwise scheme of p. 103 is adaptively CPA-secure
   (`BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa`, from `bitwise_padded_cpa` and
   `FixedLengthPKScheme.INDSecure.adaptive_cpa`).

The arithmetic efficiency premise `ArithmeticFP` and Rabin's prime-density premise `BlumDensity`
stay explicit hypotheses.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010:
  Theorems 53.2 and 57.2 (RSA), §2.12 and Theorems 61.8 and 63.10 (Rabin–Blum), Theorem 87.3
  (Goldreich–Levin),
  Algorithm 104.3 and Theorem 104.4, p. 103 (the bitwise scheme), Definition 171.5.
-/

namespace TCSlib.Cryptography.Implications.PublicKey

open TCSlib.Cryptography TCSlib.Cryptography.Composability TCSlib.Cryptography.Candidates Complexity

/-- **RSA gives adaptively CPA-secure public-key encryption with `n`-bit messages.** Under the RSA
assumption and arithmetic efficiency, some fixed-length public-key scheme with message length
`PolyExpr.var` is secure in the adaptive multi-challenge CPA game:
`ArithmeticFP → RSAAssumption →
∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa`
[PS10, Theorems 53.2 and 57.2, Theorems 87.3 and 104.4, p. 103, Definition 171.5].

**Proof sketch.** `rsaTrapdoor_oneWay` and the shift by `2`
(`TrapdoorCollection.shiftParameter_oneWay`) give a one-way trapdoor collection whose encodings have
width exactly `2(n + 2)` (`rsaTrapdoor_shiftParameter_encD_length`). Goldreich–Levin padding gives a
secure single-bit scheme (`TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`), and
`BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa` finishes. -/
theorem exists_adaptiveCPA_of_rsa (H : ArithmeticFP) (hR : RSAAssumption) :
    ∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa := by
  have hT := (rsaTrapdoor H).shiftParameter_oneWay 2 (rsaTrapdoor_oneWay H hR)
  obtain ⟨_, hE⟩ := TrapdoorCollection.OneWay.exists_glPad_singleBitSecure _
    (rsaTrapdoor_shiftParameter_encD_length H) hT
  obtain ⟨S, hmsg, -, hS⟩ := hE.exists_adaptive_cpa
  exact ⟨S, hmsg, hS⟩

/-- **Factoring gives adaptively CPA-secure public-key encryption with `n`-bit messages.** Under the
factoring assumption, the density of Blum primes and arithmetic efficiency, some fixed-length
public-key scheme with message length `PolyExpr.var` is secure in the adaptive multi-challenge CPA
game: `ArithmeticFP → BlumDensity → FactoringAssumption →
∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa`
[PS10, §2.12, Theorems 61.8 and 63.10, Theorems 87.3 and 104.4, p. 103, Definition 171.5].

**Proof sketch.** As `exists_adaptiveCPA_of_rsa`, with the Rabin–Blum trapdoor collection
(`rabinBlumTrapdoor_oneWay`) shifted by `3`, whose encodings have width exactly `2(n + 3)`
(`rabinBlumTrapdoor_shiftParameter_encD_length`). -/
theorem exists_adaptiveCPA_of_factoring (H : ArithmeticFP) (hD : BlumDensity)
    (hF : FactoringAssumption) :
    ∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa := by
  have hT := (rabinBlumTrapdoor H).shiftParameter_oneWay 3 (rabinBlumTrapdoor_oneWay H hD hF)
  obtain ⟨_, hE⟩ := TrapdoorCollection.OneWay.exists_glPad_singleBitSecure _
    (rabinBlumTrapdoor_shiftParameter_encD_length H) hT
  obtain ⟨S, hmsg, -, hS⟩ := hE.exists_adaptive_cpa
  exact ⟨S, hmsg, hS⟩

end TCSlib.Cryptography.Implications.PublicKey
