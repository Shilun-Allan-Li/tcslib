/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import TCSlib.Cryptography.Pseudorandom.Generators
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation
import TCSlib.Cryptography.Pseudorandom.Functions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Pseudorandomness

Concrete-layer formalization of [Gar26, Chapter 3]: computational indistinguishability
and hybrid arguments, pseudorandom generators (stretch extension and construction from a
one-way permutation with a hard-concentrate bit), and pseudorandom functions (the GGM
construction). Each theorem is an explicit reduction with an exact bound on advantages.

## Contents

* `Indistinguishability`: the sunglass and multicopy lemmas (Lemmas 3.2 and 3.3).
* `Generators`: the PRG advantage (Definition 3.5) and PRG extension (Theorem 3.1).
* `GeneratorFromPermutation`: a PRG from a one-way permutation (Theorem 3.2).
* `Functions`: oracle adversaries, pseudorandom functions and GGM (Theorem 3.3).

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Chapter 3.
-/
