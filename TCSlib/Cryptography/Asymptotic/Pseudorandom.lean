/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Asymptotic pseudorandomness compatibility import

## Main definitions

`TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs` defines the asymptotic
generator interface and its efficiency and security predicates.

## Main results

This import exposes the characterization of ensemble pseudorandomness by negligible
PRG advantage and the generator's security and sampling lemmas.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definitions 74.1 and 77.1.)
-/
