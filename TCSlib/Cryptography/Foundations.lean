/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.Cryptography.Foundations.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Foundations of the concrete security layer

Negligible and noticeable functions, uniform probability on finite types, and the
concrete security experiments (inversion, prediction, distinguishing) on which the
one-way function, hard-concentrate bit and pseudorandomness developments are built.

## Contents

* `Negligible`: negligible and noticeable functions and their closure properties.
* `Probability`: uniform probability `uprob`, expectation `uexp`, the union bound,
  Fubini, averaging and the hybrid argument.
* `Experiments`: `invProb`, `predProb`, `acceptProb`, `distAdv`, and the bound of
  distinguishing advantage by statistical distance.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Chapters 1–3.
-/
