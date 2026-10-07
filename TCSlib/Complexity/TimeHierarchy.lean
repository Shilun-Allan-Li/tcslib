/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.TimeHierarchy.ClockMachine
import TCSlib.Complexity.TimeHierarchy.ClockLoop
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TimeHierarchy.Diagonal
import TCSlib.Complexity.TimeHierarchy.Separation

/-!
# The Time Hierarchy Theorem

[AB09, §3.1, Theorem 3.1]: more time decides more languages. The headline results are
`Complexity.time_hierarchy` (if `g` is time constructible and `(f(n) + n + 1)² = o(g(n))`
then `DTIME(f) ⊊ DTIME(g + 1)` — quadratic overhead in place of the book's
`f log f`, see `TimeHierarchy.Diagonal` for all divergences) and its consequence
`Complexity.P_ssubset_EXP` (`P ⊊ EXP`).

## Contents

- `TimeHierarchy.ClockMachine`: the clocked runner `clockTM K W` (budget word from `K` on a
  binary counter tape; `W` run step by step against it) and its setup phases
- `TimeHierarchy.ClockLoop`: the counter loop with amortized cost analysis and the runner's
  specification `clockTM_spec`
- `TimeHierarchy.CodePrefix`: the code-prefix duplication machine `preTM`
  (`pairEncode α w ↦ pairEncode α (pairEncode α w)`) and timed partial composition
- `TimeHierarchy.Diagonal`: the diagonal language, its upper and lower bounds, and
  `Complexity.time_hierarchy` [AB09, Theorem 3.1]
- `TimeHierarchy.Separation`: `2ⁿ` is time constructible, `DTIME(nᵏ + 1) ⊊ DTIME(2ⁿ)`,
  and `P ⊊ EXP`

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1.)
-/
