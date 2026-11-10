/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Authentication.MAC.Defs
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Hashing.CollisionResistant

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compatibility import for authentication and hashing definitions

## Main definitions

The MAC, signature and collision-resistant hash interfaces are defined in
`Authentication.MAC.Defs`, `Authentication.Signatures.Defs` and `Hashing.CollisionResistant`.

## Main results

The experiment equations and security characterizations accompany those interfaces.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definitions 134.1, 134.2, 135.1, 136.2 and 140.1.
-/
