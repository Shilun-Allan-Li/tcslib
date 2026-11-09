/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.PublicKey
import TCSlib.Cryptography.Encryption.PublicKey.Scheme
import TCSlib.Cryptography.Encryption.PublicKey.HybridMachine
import TCSlib.Cryptography.Encryption.PublicKey.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Candidates.RSA
import TCSlib.Cryptography.Candidates.Rabin
import TCSlib.Cryptography.Candidates.ElGamal
import TCSlib.Cryptography.Composability.PublicKey

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-key encryption

## Main definitions

`TCSlib.Cryptography.PublicKeyScheme` and `TCSlib.Cryptography.BitPublicKeyScheme`
give the ensemble interfaces. `TCSlib.Cryptography.Composability.FixedLengthPKScheme`
supports the oracle CPA, CCA1 and CCA2 games.

## Main results

`TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme` packages a correct bit scheme.
`TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme_singleBitSecure` proves security
given one-wayness, a hard-core predicate and its efficient evaluator.
`TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise` and
`TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure` give fixed-vector
multi-message security.

## Contents

* `Scheme` defines the scheme interfaces and their correctness fields.
* `HybridMachine` builds the public-key hybrid reduction and its coin split.
* `Hybrid` proves the shared-key bound on tuples of encryptions.
* `EnsembleSecurity` gives the games, bitwise construction and fixed-vector security theorem.
* `Asymptotic.PublicKey` develops trapdoor bit encryption [PS10, §3.10].
* `OracleSecurity` gives the fixed-length scheme, codecs and oracle games [PS10, §7.1.4].
  The proof of `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa` is pending.
* `Composability.PublicKey` re-exports the oracle games and gives the trapdoor CPA corollary.
* `Candidates.RSA` constructs `TCSlib.Cryptography.Candidates.rsaTrapdoor`.
  `TCSlib.Cryptography.Candidates.rsaTrapdoor_oneWay` uses
  `TCSlib.Cryptography.Candidates.RSAAssumption`.
* `Candidates.Rabin` constructs `TCSlib.Cryptography.Candidates.rabinBlumTrapdoor`.
  `TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay` uses
  `TCSlib.Cryptography.Candidates.FactoringAssumption` and `TCSlib.Cryptography.Candidates.BlumDensity`.
* `Candidates.ElGamal` gives the group-message scheme `TCSlib.Cryptography.Candidates.elGamal`.
  `TCSlib.Cryptography.Candidates.elGamal_correct` handles admissible messages.
  `TCSlib.Cryptography.Candidates.elGamal_secure` uses
  `TCSlib.Cryptography.Candidates.DDHAssumption` for `TCSlib.Cryptography.Candidates.egGroupGen`
  and a negligible full-length exception bound for the safe-prime generator.

The three candidate routes take arithmetic efficiency as
`TCSlib.Cryptography.Candidates.ArithmeticFP`. RSA and Rabin share the trapdoor-bit route.
Its Goldreich–Levin bridge `TCSlib.Cryptography.TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`
requires the encoding-width premise `henc`. ElGamal uses its own group-message game.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/
