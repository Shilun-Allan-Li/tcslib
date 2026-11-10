/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag
import TCSlib.Cryptography.Encryption.PublicKey.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.TrapdoorPredictor
import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor
import TCSlib.Cryptography.Encryption.PublicKey.TrapdoorCPA
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
import TCSlib.Cryptography.Composability.SequentialZK
import TCSlib.Cryptography.Composability.ThreeColoring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Encryption security and sequential zero-knowledge composition

The definitions, constructions and theorem statements of [PS10, Chapter 7].
The individual modules record deviations, proof sketches and outstanding admissions.

## Main definitions

See the definitions and construction modules listed below.

## Main results

See the theorem statements and correctness results in the constituent modules.

## Contents

* `Encryption.PrivateKey.OracleSecurity` gives the private-key CPA, CCA1 and CCA2 games.
* `Encryption.PrivateKey.OracleFromPRF` gives the fixed-length PRF construction and its
  oracle security statements.
* `Encryption.PrivateKey.EncryptThenTag` gives encrypt-then-tag and its CCA2 security statement.
* `Encryption.PublicKey.OracleSecurity` gives the public-key oracle games.
* `Encryption.PublicKey.TrapdoorCPA` gives the trapdoor CPA corollary.
* `Encryption.PublicKey.NonMalleability.Indistinguishability` and
  `Encryption.PublicKey.NonMalleability.Simulation` give the two notions of non-malleability.
* `SequentialZK` — sequential repetition and zero-knowledge composition statements.
* `ThreeColoring` — the quadratic soundness estimate and sequential zero-knowledge corollary.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010.
-/
