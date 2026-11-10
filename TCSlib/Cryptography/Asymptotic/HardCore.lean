/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore.Functions
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hard-core predicates and the permutation-to-PRG route

This compatibility import brings the function-family form of Goldreich–Levin
and the asymptotic PRG construction into scope [PS10, Theorems 79.4 and 87.3].

## Contents

* `HardCore.Functions` defines hard-core predicates and proves Goldreich–Levin
  for function families.
* `Pseudorandom.Generators.Asymptotic.FromPermutation` defines and verifies
  the one-bit and iterated PRG constructions.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §§3.3–3.4.
-/
