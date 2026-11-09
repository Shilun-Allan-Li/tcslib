/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.Asymptotic.Ensembles
import TCSlib.Cryptography.Asymptotic.PublicKeyLemmas
import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-key encryption compatibility import

## Main definitions

`TCSlib.Cryptography.Encryption.PublicKey.Trapdoor` provides the trapdoor bit scheme.
Its ensemble interface also exposes the general public-key schemes.

## Main results

This import exposes the trapdoor security theorems and their Goldreich–Levin bridge.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 104.3 and Theorem 104.4.)
-/
