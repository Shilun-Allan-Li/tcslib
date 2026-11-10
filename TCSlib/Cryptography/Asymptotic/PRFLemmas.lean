/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Evaluator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compatibility import for the GGM evaluator

The evaluator, its polynomial running time, and the bit-string identities
live in `Pseudorandom.Functions.Asymptotic.GGM.Evaluator`.

## Main definitions

`ggmEval` is the bit-string evaluator.

## Main results

`ggmEval_poly` and `ggmEval_ofFn` give its time bound and correctness.

## Contents

* `TCSlib.Cryptography.Asymptotic.HardCore`
* `TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Evaluator`

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §3.8, Theorem 97.3.
-/
