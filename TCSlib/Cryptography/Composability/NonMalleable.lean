/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.PublicKey
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compatibility import for indistinguishability-based non-malleability

## Main definitions

The non-malleability game and security predicate accompany the result statements.

## Main results

`TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability` is the entry point for the relocated results.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 172.6 and Theorem 175.9.
-/
