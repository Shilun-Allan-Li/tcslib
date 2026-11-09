/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PublicKey.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.TrapdoorPredictor

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-key proof support compatibility import

## Main definitions

`Hybrid` and `TrapdoorPredictor` provide the hybrid and predictor machines.

## Main results

This import exposes the shared-key hybrid bound and the trapdoor prediction identity.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 104.3 and Theorem 104.4.)
-/
