/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.GGMReductionEval
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compatibility import for the asymptotic PRF construction

The oracle and PRF contracts and the GGM construction are available
through `Pseudorandom.Functions.Asymptotic.GGM`.

## Main definitions

`PRF` and `ggmPRF` give the security contract and construction.

## Main results

`ggmPRF_prf` and `exists_prf_of_exists_prg` give security and existence.

## Contents

* `TCSlib.Cryptography.Asymptotic.GGMReductionEval`
* `TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM`

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §3.8, Theorem 97.3.
-/
