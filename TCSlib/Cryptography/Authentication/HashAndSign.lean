/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Lamport
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compatibility import for hash-and-sign

## Main definitions

`Authentication.Signatures.HashAndSign` owns the construction.

## Main results

The correctness or efficiency lemmas and the security statement accompany the construction.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Protocol 144.2 and Theorem 144.1.
-/
