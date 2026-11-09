/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.Defs
import TCSlib.Cryptography.Composability.PRFScheme
import TCSlib.Cryptography.Composability.CCA2Scheme
import TCSlib.Cryptography.Composability.PublicKey
import TCSlib.Cryptography.Composability.NonMalleable
import TCSlib.Cryptography.Composability.SimNonMalleable
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

* `Defs` — private-key CPA, CCA1 and CCA2 security games.
* `PRFScheme` — the PRF-based encryption construction under chosen-ciphertext attacks.
* `CCA2Scheme` — encrypt-then-tag and its CCA2 security statement.
* `PublicKey` — padded public-key encryption and chosen-ciphertext games.
* `NonMalleable` — indistinguishability-based non-malleability.
* `SimNonMalleable` — simulation-based non-malleability in the cited repaired formulation.
* `SequentialZK` — sequential repetition and zero-knowledge composition statements.
* `ThreeColoring` — the quadratic soundness estimate and sequential zero-knowledge corollary.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010.
-/
