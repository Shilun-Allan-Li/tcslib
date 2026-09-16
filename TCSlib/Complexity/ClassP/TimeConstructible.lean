/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Time-constructible functions

A function `T : ℕ → ℕ` is *time constructible* if `T n ≥ n` and some machine computes,
on every input `x`, the binary representation of `T |x|` within `T |x|` steps.
[AB09, §1.3] Time constructibility rules out pathological time bounds; it is the standing
hypothesis of the timed universal machine (phase 3) and, later, of the hierarchy theorems.

## Design and deviations from [AB09]

* Binary representation is `Nat.bits` (little-endian, no leading `false`s), where [AB09]
  writes `⌞T(|x|)⌟` without fixing endianness. Nothing in Chapter 1 depends on the choice.
* **Audit flag.** [AB09] demands the computation run within exactly `T n` steps, with no
  constant slack, and then asserts that `n`, `n log n`, `n²`, `2ⁿ` are time constructible.
  For small bounds this exactness is delicate (e.g. for `T = id` the machine must emit
  all of `⌞n⌟` within `n` steps while the output tape is write-only). We state the
  faithful definition; if the exactness proves unusable, the fallback — sufficient for
  every downstream use — is to allow a constant factor, mirroring `DTIME`. No
  constructibility *instances* are claimed in this phase.

## Main definitions

* `Complexity.TimeConstructible` — [AB09, §1.3].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3, "Time-constructible functions".)
-/

namespace Complexity

open Turing

/-- `T` is time constructible: `T n ≥ n`, and some finite binary machine computes
`x ↦ ⌞T |x|⌟` (binary via `Nat.bits`) within `T |x|` steps. [AB09, §1.3] -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ T n) ∧
  ∃ M : FinTM Bool, ∀ x : List Bool,
    M.ComputesInTime x (T x.length).bits (T x.length)

end Complexity
