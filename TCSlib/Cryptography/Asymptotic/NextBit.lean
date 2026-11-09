/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.NextBit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Next-bit compatibility import

## Main definitions

This import exposes the finite experiment and the ensemble next-bit test from
`TCSlib.Cryptography.Pseudorandom.NextBit`.

## Main results

The finite bounds and both directions of the ensemble characterization are available
through this import.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 75.2 and Theorem 75.4.)
-/
