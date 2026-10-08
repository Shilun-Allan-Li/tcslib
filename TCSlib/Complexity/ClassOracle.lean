/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassOracle.Classes
import TCSlib.Complexity.ClassOracle.SATOracle

/-!
# Oracle complexity classes

[AB09, §3.4, Definition 3.5]: `Pᴼ` and `NPᴼ`, the polynomial-time classes
relative to an oracle `O`, over the bundled finite oracle machines of
`TCSlib.Complexity.TuringMachine.OracleFinite` and
`TCSlib.Complexity.TuringMachine.OracleNondeterministic`. The headline
statements of this surface (phase P3.1 of `AroraBarakChapters3-4Plan.md`) are
the workhorse `Complexity.mem_POracle_of_polyTimeReducible` (`L ≤ₚ O → L ∈ Pᴼ`),
Example 3.6's redundancy of polynomial-time oracles, and the `SAT`-oracle sanity
theorems; the relativization theorem [AB09, Theorem 3.7] is phase P3.2.

## Contents

- `ClassOracle.Classes`: `DTIMEOracle`, `NTIMEOracle`, `POracle`, `NPOracle`,
  the inclusion and closure statements, and Example 3.6(2)
- `ClassOracle.SATOracle`: Example 3.6(1) and `NP ⊆ P^SAT` / `coNP ⊆ P^SAT`

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4.)
-/
