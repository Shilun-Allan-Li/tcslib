/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.OneWayFunctions.Basic
import TCSlib.Cryptography.OneWayFunctions.Robustness
import TCSlib.Cryptography.OneWayFunctions.Brittleness
import TCSlib.Cryptography.OneWayFunctions.OutputLength
import TCSlib.Cryptography.OneWayFunctions.Amplification

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One-way functions, concrete layer

The reductions of [Gar26, Chapter 2, §§2.2–2.4] at one fixed value of the security
parameter: each reduction is an explicit adversary built from a given one, and each
result is an exact inequality between inversion probabilities.

## Contents

* `TCSlib.Cryptography.OneWayFunctions.Basic`: uniform-probability toolkit (averaging,
  conditioning on a bad set, independent coordinates, planting into a uniform tuple).
* `TCSlib.Cryptography.OneWayFunctions.Robustness`: redefining a function on a set `S`
  (§2.2.1), with the missing collision term and a counterexample to the source's example.
* `TCSlib.Cryptography.OneWayFunctions.Brittleness`: `f ∘ f` for `f(x₁, x₂) = 0ⁿ‖g(x₁)`,
  and dropping the first output bit (Claims 2.1 and 2.2) (§2.2.2).
* `TCSlib.Cryptography.OneWayFunctions.OutputLength`: padding (Lemma 2.3) and functions
  with `⌊log₂ n⌋`-bit outputs (Exercise 2.4).
* `TCSlib.Cryptography.OneWayFunctions.Amplification`: Yao's hardness amplification
  (Theorem 2.1, Figure 2.2) with explicit repetition count and threshold.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Chapter 2.
-/
