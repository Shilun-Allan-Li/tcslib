/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.Arithmetic
import TCSlib.Cryptography.Candidates.Concrete
import TCSlib.Cryptography.Candidates.Factoring
import TCSlib.Cryptography.Candidates.RSA
import TCSlib.Cryptography.Candidates.Rabin
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.Candidates.DiscreteLogHardcore
import TCSlib.Cryptography.Candidates.ElGamal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Candidate one-way functions and collections

The number-theoretic candidates of [PS10, §2.3, §2.7–§2.12 and §3.10]: `f_mult` and the
factoring assumption, the factoring, RSA, Rabin and discrete-logarithm collections, the
hard-core bit of the discrete logarithm and El Gamal encryption. Every theorem about
machines is conditional on the arithmetic hypothesis bundle
`TCSlib.Cryptography.Candidates.ArithmeticFP` (plan decision "conditional candidates",
foundation decision D11): the repository has no machines for binary arithmetic, so their
polynomial-time computability is an explicit hypothesis, never an axiom.

## Contents

* `Arithmetic` — the hypothesis bundle `ArithmeticFP` (binary multiplication, addition,
  truncated subtraction, division with remainder, extended Euclid, modular exponentiation,
  comparison, bit length, primality testing; `add`/`sub`/`size` added by the run-3 audit
  repair P7-1) and the fixed-width binary numerals `natToBits`/`natToList` with their
  round-trip lemmas.
* `Concrete` — the concrete-layer lemmas of the factoring reductions: conditioning on an
  event (C1), the diagonal, random-position planting with a good set (C3), the tail bounds
  `(1 - 1/a)^{ak} ≤ e^{-k}` (C8, [PS10, Claim 36.2]), prime-pair density on bit strings,
  the type `DistinctPrimes` of pairs of distinct primes with its encoding and totient, and
  the block rejection sampler `rejectBlocksL` on coin lists shared by the honest samplers
  (run-3 audit P7-6).
* `Factoring` — `f_mult` [PS10, Definition 29.1], the factoring assumption
  [PS10, Assumption 30.1], the one-call reduction [PS10, Algorithm 33.6] and Claim 34.1,
  `f_mult` weakly one-way [PS10, Theorem 33.5], the random-planting reduction
  [PS10, Algorithm 37.4] and `f_mult^{4n³}` strongly one-way [PS10, Theorem 36.3], the
  factoring collection [PS10, Theorem 51.1].
* `RSA` — the RSA assumption and collection [PS10, Assumption 53.1, Theorems 53.2, 55.2,
  57.2, Algorithm 55.3].
* `Rabin` — the Rabin collection and trapdoor permutation [PS10, Theorems 61.7, 61.8,
  63.10, Algorithm 62.9, Claim 62.2].
* `DiscreteLog` — the discrete-logarithm assumption and collection
  [PS10, Assumption 52.2, Theorem 52.3].
* `DiscreteLogHardcore` — the hard-core bit of the discrete logarithm
  [PS10, Lemma 84.1, Algorithm 84.2].
* `ElGamal` — the DDH assumption and El Gamal encryption [PS10, Assumption 105.1,
  Algorithm 106.2, Theorem 107.3].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026.
-/
