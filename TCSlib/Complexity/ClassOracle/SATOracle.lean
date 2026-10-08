/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassOracle.Classes
import TCSlib.Complexity.ClassNP.CoNP
import TCSlib.Complexity.CookLevin.Hardness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `SAT` oracle: Example 3.6(1) and the `NP ⊆ P^SAT` sanity theorem

[AB09, Example 3.6(1)]: with oracle access to `SAT`, the complement of `SAT` is
decidable in polynomial time — query the oracle on the input and give the
opposite answer. Together with `SAT`'s `NP`-hardness (the Cook-Levin theorem,
`Complexity.SAT_NPHard`), the same one-query pattern puts all of `NP`, and by
complementation all of `coNP`, inside `P^SAT`. These are the standing sanity
checks that the `Complexity.POracle` interface composes with the chapter-2
surface before the relativization theorem (phase P3.2) builds on it.

## Main results (all sorried; phase-P3.1 statements)

* `Complexity.compl_SAT_mem_POracle_SAT` — `SATᶜ ∈ P^SAT`.
  [AB09, Example 3.6(1)]
* `Complexity.NP_subset_POracle_SAT` — `NP ⊆ P^SAT`.
* `Complexity.coNP_subset_POracle_SAT` — `coNP ⊆ P^SAT`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Example 3.6(1).)
-/

namespace Complexity

open Turing

/-- **With a `SAT` oracle, unsatisfiability is easy**: `SATᶜ ∈ P^SAT` — query
the oracle on the input formula and answer the opposite.
[AB09, Example 3.6(1), with the book's `co-SAT` rendered as the set complement
`SATᶜ`, so no formula-syntax carrier is involved]

**Proof sketch.** `Complexity.oracle_mem_POracle` gives `SAT ∈ P^SAT`;
`Complexity.compl_mem_POracle` flips the answer. -/
theorem compl_SAT_mem_POracle_SAT : (SATᶜ : Language Bool) ∈ POracle SAT := by
  sorry

/-- **Everything in `NP` is one `SAT`-query away**: `NP ⊆ P^SAT`.

**Proof sketch.** For `L ∈ NP`, Cook-Levin (`Complexity.SAT_NPHard`) gives
`L ≤ₚ SAT`, and `Complexity.mem_POracle_of_polyTimeReducible` turns the
reduction into a one-query oracle machine. -/
theorem NP_subset_POracle_SAT : NP ⊆ POracle SAT := by
  sorry

/-- **And so is everything in `coNP`**: `coNP ⊆ P^SAT`.

**Proof sketch.** `L ∈ coNP` means `Lᶜ ∈ NP`; `Complexity.NP_subset_POracle_SAT`
puts `Lᶜ` in `P^SAT`, and `Complexity.compl_mem_POracle` closes under the
complement back to `L`. -/
theorem coNP_subset_POracle_SAT : coNP ⊆ POracle SAT := by
  sorry

end Complexity
