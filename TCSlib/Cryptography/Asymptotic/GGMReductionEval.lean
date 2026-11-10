/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.GGMReduction
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compatibility import for the GGM machine run

The reduction machine and its agreement with the finite distinguisher
live in `Pseudorandom.Functions.Asymptotic.GGM.Run`.

## Main definitions

`GGMRed.ggmRedMachine` is the non-uniform reduction machine.

## Main results

`GGMRed.ggmRedMachine_distinguisher` gives its run agreement.

## Contents

* `TCSlib.Cryptography.Asymptotic.GGMReduction`
* `TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run`

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §3.8, Theorem 97.3.
-/
