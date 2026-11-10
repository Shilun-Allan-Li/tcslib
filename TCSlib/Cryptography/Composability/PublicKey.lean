/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.PublicKey
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.TrapdoorCPA

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compatibility import for the public-key oracle games and trapdoor CPA corollary

## Main definitions

The fixed-length oracle games are defined in `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity`.

## Main results

`TCSlib.Cryptography.Encryption.PublicKey.TrapdoorCPA` is the entry point for the relocated results.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Claim 172.a.
-/
