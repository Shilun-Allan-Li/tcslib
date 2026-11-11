/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From one challenge to adaptively many under chosen-plaintext attack

For a public-key scheme, security in the single-challenge CPA game of [PS10, Definition 171.5]
implies security in the adaptive left-or-right game with a polynomial number of fresh
challenges (`FixedLengthPKScheme.AdaptiveINDSecure`). The argument is the single-to-many hybrid
lifting of [PS10, p. 103] and [Pas09, Theorem 2], stated there for fixed message vectors and
extended here to adaptively chosen challenges: the adversary holds the public key, so a
reduction can produce every challenge but one itself.

## Main results

* `Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa` (stated; a `sorry` under its
  sketch): single-challenge CPA security gives adaptive multi-challenge CPA security.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 171.5 (book p. 171) and the single-to-many hybrid argument (book p. 103).
* [Pas09] R. Pass, *Cornell CS 6830, lecture 13* (2009), §1 and Theorem 2.
-/

namespace TCSlib.Cryptography.Composability.FixedLengthPKScheme

open Complexity Turing TCSlib.Cryptography.Games

/-- **Single-challenge CPA security gives adaptive multi-challenge CPA security**: if every
efficient adversary has negligible advantage in the CPA game with one challenge, then every
efficient adversary has negligible advantage in the adaptive left-or-right CPA game with a
polynomial challenge cap `cap(n)` and query budget `q(n)` [PS10, Definition 171.5; the
single-to-many hybrid argument of p. 103, extended to adaptive challenges].

**Proof sketch.**
1. Fix `A`, `q` and `cap`. For `i ≤ cap(n)` let `H_i` be the adaptive CPA experiment in which the
   first `i` fresh challenges encrypt the right message and the later ones the left message. Then
   `H_0` is the experiment with `b = false` and `H_{cap(n)}` the one with `b = true`: a challenge
   past the cap only repeats the latest ciphertext (`adaptiveIndImpl_challenge_full`), and under CPA
   `Dec` answers `⊥` whatever the history (`indImpl_dec_cpa`, `adaptiveIndImpl_dec_issued`).
2. By `Games.exists_advantage_hybrid_gap`, at each `n` with `cap(n) > 0` some `i⋆(n) < cap(n)`
   has `advantage(H_{i⋆}, H_{i⋆+1}) ≥ advantage(H_0, H_{cap(n)}) / cap(n)`; the case `cap(n) = 0`
   has advantage `0`.
3. The single-challenge adversary `B` takes `i⋆(n)` as advice. On `pk` it runs `A`, answers `Dec`
   with `⊥`, answers the first `i⋆` fresh challenges with encryptions of the right message and
   the fresh challenges after the `(i⋆+1)`-st with encryptions of the left message, computed with
   `Enc` on `pk` and its own coins, forwards the `(i⋆+1)`-st to its own `Challenge` oracle, repeats
   the latest ciphertext past the cap, and outputs `A`'s bit. Then `B`'s game with bit `b` is
   `H_{i⋆+b}`. `B` is a non-uniform PPT playing the outer game by
   `Games.exists_interactiveHandlerMachine` (T2): the handler's state holds the challenge count,
   the latest ciphertext and `i⋆(n)` (its initial state, an arbitrary function of `n`), its seed
   is `cap(n)` encryption tapes, its one outer call is the `(i⋆+1)`-st challenge, and its run is
   polynomial-time because `Enc` is uniform and polynomial-time.
4. `B` makes at most `q(n)·perCall + finCall` outer queries, a polynomial, so `h` bounds its
   advantage by a negligible `ε`. Hence `A`'s advantage is at most `cap(n) · ε(n)`, negligible
   by `Negligible.polyExpr_mul` (`Asymptotic/ReductionSupport`) with the polynomial `cap`. -/
theorem INDSecure.adaptive_cpa {S : FixedLengthPKScheme} (h : S.INDSecure .cpa) :
    S.AdaptiveINDSecure .cpa := by
  sorry

end TCSlib.Cryptography.Composability.FixedLengthPKScheme
