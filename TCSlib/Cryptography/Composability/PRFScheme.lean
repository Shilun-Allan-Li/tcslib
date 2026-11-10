/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.Defs
import TCSlib.Cryptography.Asymptotic.MultiMessage
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fixed-length PRF encryption compatibility import

## Main definitions

`Encryption.PrivateKey.OracleFromPRF` wraps the PRF encryption scheme with its fixed
ciphertext length. The declarations live in `TCSlib.Cryptography.Composability`.

## Main results

This import exposes the CPA and CCA1 statements, the CCA2 counterexample statement
and the negation derived from it.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 99.1, Theorem 168.2 and §7.1.3.)
-/
