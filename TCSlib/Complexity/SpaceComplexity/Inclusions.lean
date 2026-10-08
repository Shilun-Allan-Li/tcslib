/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.SpaceClasses
import TCSlib.Complexity.ClassNP.SAT

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Time against space: the easy inclusions

The first two inclusions of [AB09, Theorem 4.2]
(`DTIME(S) ⊆ SPACE(S) ⊆ NSPACE(S)`), the polynomial-level corollaries on the
p. 92 chain (`P ⊆ PSPACE`), and the certificate-cycling memberships of
[AB09, Example 4.6] (`NP ⊆ PSPACE`, `3SAT ∈ PSPACE`). The third inclusion of
Theorem 4.2 (`NSPACE(S) ⊆ DTIME(2^{O(S)})`) needs the configuration-graph layer
and is phase P4.2; the parity example of [AB09, Example 4.7] lives in
`TCSlib.Complexity.SpaceComplexity.Examples`.

## Main results (sorried; phase-P4.1 statements)

* `Complexity.DTIME_subset_SPACE` — [AB09, Theorem 4.2, first inclusion].
* `Complexity.P_subset_PSPACE` — the polynomial corollary.
* `Complexity.NP_subset_PSPACE` — [AB09, Example 4.6].
* `Complexity.SAT3_mem_PSPACE` — [AB09, Example 4.6].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Theorem 4.2, Example 4.6.)
-/

namespace Complexity

open Turing

/-- **Time bounds space**: `DTIME T ⊆ SPACE T` — a machine can visit at most one
new cell per head per step. [AB09, Theorem 4.2, first inclusion]

**Proof sketch.** Let `M` decide `L` within `c · T n` steps. Each of `M`'s `k`
work-tape heads visits at most `c · T n + 1` cells in `c · T n` steps
(`Turing.MultiTapeTM.visitedByTapeHead` is an image of `Finset.range
(c·T n + 1)`, so `Finset.card_image_le` bounds it), hence
`spaceUsed ≤ k · (c · T n + 1) ≤ (k · c + k) · T n` whenever `T n ≥ 1`. If
`T n = 0` for some `n` then every `c · T` vanishes there and `DTIME T = ∅` by
the `Complexity.DTIME_eq_empty_of_exists_zero` argument (no machine halts in
`0` steps from a live initial state), so the inclusion is vacuous. The space
witness reuses `M` itself with the absorbed constant `k · c + k`, and the
halting time `c · T |x|` instantiates `Turing.FinTM.ComputesInSpace`'s
existential time. -/
theorem DTIME_subset_SPACE (T : ℕ → ℕ) : DTIME T ⊆ SPACE T := by
  sorry

/-- `P ⊆ PSPACE` — the polynomial-level corollary, on the p. 92 chain.

**Proof sketch.** Degree by degree: `DTIME (n^c + 1) ⊆ SPACE (n^c + 1)` by
`Complexity.DTIME_subset_SPACE`, then `Set.iUnion_mono` across the unions
defining `Complexity.P` and `Complexity.PSPACE`. -/
theorem P_subset_PSPACE : P ⊆ PSPACE := by
  sorry

/-- **Certificates can be cycled through in polynomial space**: `NP ⊆ PSPACE`.
[AB09, Example 4.6: "a similar idea of cycling through all potential
certificates applies to any NP language"]

**Proof sketch.** Let `L ∈ NP` with verifier language `V ∈ P` and certificate
length `C·(n+1)^c` (`Complexity.mem_NP_iff`-shape data). Fill obligations,
named for the brief: (i) a certificate enumerator holding the current
certificate `u` on a work tape and stepping it in place by fixed-width binary
increment (`incrementTM`, P11/§12 R3 — the space-annotated form), never using
more than `C·(n+1)^c + O(1)` cells; (ii) for each `u`, a run of `V`'s decider
on the **virtual input** `x ++ u` assembled from the input tape and the
certificate tape (the virtual-input idiom of
`TCSlib.Complexity.TuringMachine.UniversalStartup`), with the decider's space
bounded through `Complexity.DTIME_subset_SPACE` applied to `V`'s polynomial
time bound — this is where the run is *re-executed* rather than stored, the
space-reuse point of [AB09, Example 4.6]; (iii) accept as soon as one `u`
verifies, reject after the last. Total space: certificate + decider + control,
all polynomial in `n`. (The decider-subroutine space composition is a §12
space-clause consumer — `machine-library-design.md` §12, R1/R3.) -/
theorem NP_subset_PSPACE : NP ⊆ PSPACE := by
  sorry

/-- `3SAT` is decidable in polynomial space. [AB09, Example 4.6]

**Proof sketch.** `Complexity.SAT3_mem_NP` with `Complexity.NP_subset_PSPACE`.
Delivered strength: **polynomial** space (the route through arbitrary `NP`
membership fixes no degree); the book example's sharper linear-space direct
machine is not claimed (P4.1 round 1, note 9). -/
theorem SAT3_mem_PSPACE : SAT3 ∈ PSPACE := by
  sorry

end Complexity
