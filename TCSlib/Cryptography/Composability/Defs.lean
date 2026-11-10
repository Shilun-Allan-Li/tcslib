/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Encryption
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Private-key oracle security compatibility import

## Main definitions

`Encryption.PrivateKey.OracleSecurity` defines the fixed-length scheme interface and the
CPA, CCA1 and CCA2 experiments. The declarations live in `TCSlib.Cryptography.Composability`.

## Main results

This import exposes the oracle equations, the challenge refusal rule and the security
predicate for each attack model.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§7.1.1, Definition 168.1.)
-/
