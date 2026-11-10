/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.Defs
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.PRF
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Tagged private-key encryption compatibility import

## Main definitions

`Encryption.PrivateKey.EncryptThenTag` gives the tagged scheme as a fixed-length private-key
scheme in the `TCSlib.Cryptography.Composability` namespace.

## Main results

This import exposes the correctness and ciphertext length proofs and the CCA2 security
statement for the tagged construction.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§7.1.3, Algorithm 169.3 and Theorem 170.4.)
-/
