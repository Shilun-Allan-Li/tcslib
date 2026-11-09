/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.PublicKey
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Trapdoor encryption in the public-key CPA game

This module provides the original public-key game import through
`TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity`.

## Main definitions

`OracleSecurity` defines the fixed-length public-key scheme, its codecs and its security games.

## Main results

`TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme_padded_cpa` applies the
ensemble-to-CPA bridge to the trapdoor construction of Algorithm 104.3.
It uses the stated `BitPublicKeyScheme.SingleBitSecure.padded_cpa` bridge.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 104.3, Theorem 104.4 and Claim 172.a.)
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- **Claim 172.a: Algorithm 104.3 is CPA-secure** [PS10, p. 172: "the encryption scheme in
Construction 104.3 is CPA secure"], padded to any admissible length `L`, under the hypotheses of
[PS10, Theorem 104.4]: a collection of trapdoor permutations with a hard-core predicate `h`. -/
theorem _root_.TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme_padded_cpa
    (T : TrapdoorCollection) {h : ∀ i, T.D i → Bool} (E : T.toCollection.PredEvaluator h)
    (hT : T.OneWay) (hHC : T.toCollection.HardCore h) (L : PolyExpr)
    (hL : ∀ n (rg : (T.tdpBitScheme E).gen.Coins n) (b : Bool)
      (re : (T.tdpBitScheme E).enc.Coins n),
      2 * ((T.tdpBitScheme E).enc.runAt n
        (pairEncode (pairFstD ((T.tdpBitScheme E).gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : ((T.tdpBitScheme E).padded L hL hmsg).INDSecure .cpa :=
  (T.tdpBitScheme_singleBitSecure E hT hHC).padded_cpa L hL hmsg

end TCSlib.Cryptography.Composability
