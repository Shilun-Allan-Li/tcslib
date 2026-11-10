/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PrivateKey.Scheme
import TCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Asymptotic.MultiMessageLemmas
import TCSlib.Cryptography.Asymptotic.MultiMessage
import TCSlib.Cryptography.Composability.Defs
import TCSlib.Cryptography.Composability.PRFScheme
import TCSlib.Cryptography.Composability.CCA2Scheme

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Private-key encryption

The ensemble games compare one ciphertext or a fixed vector of ciphertexts.
The oracle games give the adversary a query budget and specify its access to
encryption, the challenge and decryption.

## Main definitions

`TCSlib.Cryptography.PrivateKeyScheme` packages uniform polynomial-time algorithms
for key generation, encryption and decryption, with perfect correctness [PS10, Definition 24.7].
`TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure` and
`TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure` give the two ensemble games
[PS10, Definitions 91.1 and 93.1].
`TCSlib.Cryptography.Composability.FixedLengthScheme` adds a ciphertext length.
Its `indGame` defines the adaptive CPA, CCA1 and CCA2 games. `INDSecure` requires
negligible advantage in the selected game [PS10, Definition 168.1].

## Main results

`TCSlib.Cryptography.prgScheme_singleMessageSecure` proves single-message security
for the pad scheme given a secure PRG and a matching efficient evaluator
[PS10, Theorem 92.2].
`TCSlib.Cryptography.prfScheme_multiMessageSecure` proves security for fixed vectors
encrypted under one key with independent coins, given a PRF and a matching efficient
evaluator [PS10, Theorem 99.2].
`TCSlib.Cryptography.exists_multiMessageSecure_of_exists_prg` composes GGM with
the PRF scheme [PS10, Theorems 97.3 and 99.2].

## Contents

* `Encryption.PrivateKey.Scheme` gives the uniform polynomial-time scheme interface.
* `Encryption.PrivateKey.EnsembleSecurity` gives the ensemble games and their relations.
* `Encryption.PrivateKey.FromPRG` gives the PRG pad construction and its security proof.
* `Asymptotic.MultiMessageLemmas` gives the encoding identities and reduction machine
  for the PRF scheme.
* `Asymptotic.MultiMessage` gives the PRF construction, its finite hybrid bound
  and its fixed-vector security proof [PS10, Algorithm 99.1 and Theorem 99.2].
* `Composability.Defs` gives the fixed-length interface and adaptive oracle games.
* `Composability.PRFScheme` gives the fixed-length version of the PRF scheme.
  The CPA and CCA1 proofs `prfFixedScheme_cpa` and `prfFixedScheme_cca1` are pending
  [PS10, Theorem 168.2]. The CCA2 counterexample `prfFixedScheme_not_cca2` is also
  pending, and `not_prfFixedScheme_cca2` depends on it.
* `Composability.CCA2Scheme` gives the encrypt-then-tag scheme, which tags the
  whole ciphertext under an independent key [PS10, Algorithm 169.3].
  The CCA2 proof `ccaScheme_cca2` is pending [PS10, Theorem 170.4].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §2.1, §§3.6–3.9 and §7.1.3.
-/
