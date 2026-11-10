/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.NonMalleable
import Mathlib.Tactic.Simps.Basic
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compatibility import for simulation-based non-malleability

## Main definitions

The message sampler, experiments and security predicate accompany the result statements.

## Main results

`TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation` is the entry point for the relocated results.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 173.7 and Theorem 174.8.
-/
