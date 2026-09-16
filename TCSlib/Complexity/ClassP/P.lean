/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class P

`P` is the class of languages decidable in polynomial time: the union over `c` of
`DTIME (n^c)`. [AB09, Definition 1.13]

## Design and deviations from [AB09]

* We take the union of `DTIME (fun n => n ^ c + 1)` over all `c : ℕ` where [AB09] writes
  `⋃_{c ≥ 1} DTIME(n^c)`. The `+ 1` repairs the empty-input degeneracy: a machine needs
  at least one step to halt, so no language whatsoever is decided within `c · 0^d = 0`
  steps on the empty input, and the literal [AB09] definition would (vacuously) exclude
  even constant-time machines on that input. For `n ≥ 1` the bounds `c · (n^d + 1)` and
  `c' · n^d` sandwich each other, so this is the standard reading of the same class.
  Ranging over `c = 0` too is harmless: `n^0 + 1 = 2` is a constant bound, subsumed by
  larger `c`.

## Main definitions

* `Complexity.P` — [AB09, Definition 1.13].

## Main results

* `Complexity.dtime_poly_subset_P` — each `DTIME (n^c + 1)` is contained in `P`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definition 1.13.)
-/

namespace Complexity

/-- The class of polynomial-time decidable languages:
`P = ⋃ c, DTIME (n^c + 1)`. [AB09, Definition 1.13] -/
def P : Set (Language Bool) := ⋃ c : ℕ, DTIME fun n => n ^ c + 1

/-- Every fixed-degree polynomial time class is contained in `P`. -/
theorem dtime_poly_subset_P (c : ℕ) : DTIME (fun n => n ^ c + 1) ⊆ P :=
  Set.subset_iUnion (fun c : ℕ => DTIME fun n => n ^ c + 1) c

/-- Membership in `P` from a concrete polynomial bound: if `L` is decidable within any
time bound that is eventually dominated by a polynomial, then `L ∈ P`.

**Proof sketch.** Pick `c` and `d` with `T n ≤ c * (n ^ d + 1)` for all `n`. By
`Complexity.DTIME.mono`, `DTIME T ⊆ DTIME (fun n => c * (n ^ d + 1))`; the latter equals
a subclass of `DTIME (fun n => n ^ d + 1)` because the constant `c` is absorbed by the
existential constant in the definition of `DTIME` (the two constants multiply). Conclude
with `Complexity.dtime_poly_subset_P`. -/
theorem mem_P_of_dtime_le {L : Language Bool} {T : ℕ → ℕ}
    (hL : L ∈ DTIME T) (c d : ℕ) (hT : ∀ n, T n ≤ c * (n ^ d + 1)) : L ∈ P := by
  sorry

end Complexity
