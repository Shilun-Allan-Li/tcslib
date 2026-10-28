/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.NumberTheory.Chebyshev
import TCSlib.Cryptography.NumberTheory.Euclid
import TCSlib.Cryptography.NumberTheory.ModExp
import TCSlib.Cryptography.NumberTheory.Units
import TCSlib.Cryptography.NumberTheory.Primality
import TCSlib.Cryptography.NumberTheory.QuadraticResidues

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Computational number theory for the candidate one-way functions

The number theory of [PS10, §2.3.2 and §2.6–§2.12] on which the factoring, RSA and Rabin
candidates of [PS10, ch. 2] rest: the density of primes, the extended Euclidean algorithm,
modular exponentiation, the group `Z_N^*` with Euler's theorem and the RSA permutation,
the Miller–Rabin test with the prime sampler, and the theory of square roots modulo primes
and products of two primes. Everything is concrete mathematics over `Nat`, `ZMod` and the
uniform probability `uprob`; machine-level statements ("polynomial time") appear only as
explicit hypotheses or as operation counts (foundation decision D11).

## Contents

- `NumberTheory.Chebyshev`: `Π_n`, Chebyshev's bound `π(x) ≥ x / (2 log₂ x)` and the
  `1/(2n)` density of primes among `n`-bit numbers [PS10, Theorem 31.3, Claim 32.4, p. 33].
- `NumberTheory.Euclid`: `ExtendedEuclid` with its call bound and correctness
  [PS10, Algorithm 43.2, Claims 43.3 and 44.5].
- `NumberTheory.ModExp`: repeated squaring with its operation count
  [PS10, Algorithm 45.5, Theorem 45.6].
- `NumberTheory.Units`: `Z_N^*`, `Φ(pq)`, exponent reduction modulo `Φ(N)`, the RSA
  permutation and the density of units [PS10, Theorem 46.8, Claim 47.2,
  Corollary 48.12, Theorem 54.3].
- `NumberTheory.Primality`: the Miller–Rabin liar set and test, `SamplePrime`
  [PS10, Algorithms 49.13 and 50.16, Theorem 49.14, Lemmas 50.15 and 51.17].
- `NumberTheory.QuadraticResidues`: `QR_N`, square roots modulo `p ≡ 3 (mod 4)`, the CRT on
  unit groups, the four-to-one squaring map, Blum integers
  [PS10, Lemma 57.1, Theorems 58.2, 58.3, 59.4, 60.5, Corollary 60.6, §2.12.1].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/
