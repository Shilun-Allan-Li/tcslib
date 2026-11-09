/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PublicKey.ElGamal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# ElGamal compatibility import

## Main definitions

This import exposes the group-message scheme from
`TCSlib.Cryptography.Encryption.PublicKey.ElGamal` and its safe-prime DDH assumption.

## Main results

The construction module gives `elGamal_correct` and `elGamal_secure`.
The fully qualified declaration names are available through this import.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 106.2 and Theorem 107.3.)
-/
