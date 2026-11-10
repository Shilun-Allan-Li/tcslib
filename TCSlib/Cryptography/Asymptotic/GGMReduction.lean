/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.PRFLemmas
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compatibility import for the GGM reduction

The reduction's lazy table, lookup loop, machine components, and time bounds
live in `Pseudorandom.Functions.Asymptotic.GGM.Reduction`.

## Main definitions

`GGMRed.lookup` and `GGMRed.rawFun` implement the reduction.

## Main results

`GGMRed.lookup_poly` and `GGMRed.rawFun_poly` give the time bounds.

## Contents

* `TCSlib.Cryptography.Asymptotic.PRFLemmas`
* `TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction`

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §3.8, Theorem 97.3.
-/
