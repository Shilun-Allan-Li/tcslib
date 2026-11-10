/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Defs
import TCSlib.Cryptography.Asymptotic.Encryption
import TCSlib.Cryptography.Asymptotic.PRF
import Mathlib.Tactic.Simps.Basic
import TCSlib.Cryptography.Authentication.MAC.FromPRF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compatibility import for the PRF-based MAC

## Main definitions

`Authentication.MAC.FromPRF` owns the PRF-based MAC and its tagging and verification functions.

## Main results

The correctness proof and security statement accompany the construction in that module.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Protocol 134.3 and Theorem 135.4 (book pp. 134–135).
-/
