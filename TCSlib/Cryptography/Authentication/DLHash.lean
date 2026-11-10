/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Defs
import TCSlib.Cryptography.Candidates.DiscreteLog
import Mathlib.Tactic.Simps.Basic
import TCSlib.Cryptography.Hashing.FromDiscreteLog

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compatibility import for the discrete-log hash family

## Main definitions

`Hashing.FromDiscreteLog` owns the construction.

## Main results

The correctness or efficiency lemmas and the security statement accompany the construction.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Protocol 142.2 and Theorem 142.3.
-/
