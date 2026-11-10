/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Pseudorandom
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Private-key encryption compatibility import

## Main definitions

`Encryption.PrivateKey.Scheme` gives the uniform scheme interface,
`Encryption.PrivateKey.EnsembleSecurity` gives the ensemble games, and
`Encryption.PrivateKey.FromPRG` gives the pseudorandom pad construction.

## Main results

This import exposes the ensemble security results and the single-message security
proof for the PRG construction.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definitions 24.7, 91.1 and 93.1, Algorithm 92.1 and Theorems 92.2 and 94.2.)
-/
