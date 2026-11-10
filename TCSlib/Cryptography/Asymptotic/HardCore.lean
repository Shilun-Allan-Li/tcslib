/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore.Functions
import TCSlib.Cryptography.Asymptotic.HardCoreCollection
import TCSlib.Cryptography.Asymptotic.HardCorePermutation.GoldreichLevin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Asymptotic hard-core predicates and Goldreich–Levin

The Goldreich–Levin theorem gives an efficiently computable hard-core bit for
the padded one-way function [PS10, Theorem 87.3]. This facade collects its
function-family, collection, and balanced-permutation forms.

## Contents

* `HardCore.Functions` defines hard-core predicates and proves Goldreich–Levin
  for function families.
* `HardCoreCollection` proves the theorem for collections, including
  collections of trapdoor permutations.
* `HardCorePermutation.GoldreichLevin` proves the balanced-permutation version.

The generator constructions and their security proofs are in
`Pseudorandom.Generators.Asymptotic.FromPermutation`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §§3.3–3.4.
-/
