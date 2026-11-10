/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreClaims
import TCSlib.Cryptography.Asymptotic.HardCorePermutation.GoldreichLevin
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hard-core bits from one-way permutations

This compatibility import keeps the balanced Goldreich–Levin result, the
concrete claims and the resulting PRG existence theorem in scope.

## Contents

* `HardCorePermutation.GoldreichLevin` supplies the balanced permutation
  and hard-core bit [PS10, Theorem 87.3].
* `HardCoreClaims` gives the concrete claims in the Goldreich–Levin proof.
* `Pseudorandom.Generators.Asymptotic.FromPermutation` proves that one-way
  permutations imply secure pseudorandom generators [PS10, §3.4, p. 84].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §3.4.
-/
