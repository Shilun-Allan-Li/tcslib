/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Savitch's theorem

[AB09, Theorem 4.14] ([Sav70]): for space-constructible `S`,
`NSPACE(S(n)) ⊆ SPACE(S(n)²)` — nondeterministic space costs only a quadratic
deterministic overhead, via the midpoint recursion `reach?(u, v, i)` over the
configuration graph of `TCSlib.Complexity.SpaceComplexity.ConfigGraph`. The
corollary `PSPACE = NPSPACE` ([AB09, §4.2.1]) closes the polynomial level.
Phase P4.2 of `AroraBarakChapters3-4Plan.md`.

**Status: statement skeleton (phase P4.2).** Every contract is sorried with a
sketch naming its fill obligations. The `SpaceComplexity.lean` facade has
carried this module since the P4.1 gate closed (root-wired while that gate
was live).

## Design

* **The positive-bound convention is respected without side conditions**:
  `Complexity.SpaceConstructible` bundles `logSpace n ≤ S n`, so `S` and
  `S · S` are everywhere positive and the P0-adopted convention
  (`TCSlib.Complexity.SpaceComplexity.ZeroSpace`) imposes no extra hypothesis.
* **The recursion is realized iteratively**: `reach?`'s call stack becomes an
  explicit stack of `O(S)`-bit frames (coded vertices and a midpoint cursor)
  on a dedicated bank, walked by the loop combinator — the §12 layer
  (`Build/Embed.lean`, `Build/Seam.lean`, `Build/Catalog.lean`) is the
  intended engine, with the depth `O(S)` and frame size `O(S)` giving the
  `O(S²)` ledger.

## Main results (all sorried; phase-P4.2 statements)

* `Complexity.spaceConstructible_poly` — the polynomial bounds of the
  campaign's normal form are space-constructible (degree at least one).
* `Complexity.savitch` — [AB09, Theorem 4.14].
* `Complexity.PSPACE_eq_NPSPACE` — [AB09, §4.2.1].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14; §4.1.2.)
* [Sav70] W. J. Savitch, *Relationships between nondeterministic and
  deterministic tape complexities*, JCSS 4(2), 1970. (Cited through [AB09];
  no external text is required for this audit.)
-/

namespace Complexity

open Turing

/-- **The campaign's polynomial bounds are space-constructible** (spec, fill
pending — phase P4.2): for `1 ≤ c`, the normal-form bound `n ^ c + 1` is
`Complexity.SpaceConstructible`. (Degree zero is excluded: `n ^ 0 + 1 = 2`
fails the bundled `logSpace n ≤ S n` at large `n`; consumers route degree
zero through monotonicity into degree one.)

**Proof sketch.** Dominance: `logSpace n ≤ n + 1 ≤ n ^ c + 1` for `1 ≤ c`
(`logSpace n ≤ n + 1` by induction on the binary length; `n ≤ n ^ c` for
`n ≥ 1`, and the `n = 0` case is `1 ≤ 1`). The witness machine computes
`(n ^ c + 1).bits` within `O(n ^ c)` visited cells: a unary power bank built
by `c` nested input scans (the `polyUnary` catalog row with its space clause,
`Turing.FinTM.computesFunInTime_polyUnary_spaceUsed`,
`Build/Catalog.lean`), then a unary-to-binary count-down into a binary counter
(`incrementTM`'s discipline; the `polyBits` row's space clause gives the
assembled bound). Named fill obligations: the two catalog instantiations and
the `ComputesInSpace` repackaging of their joint time/space contracts. -/
theorem spaceConstructible_poly (c : ℕ) (hc : 1 ≤ c) :
    SpaceConstructible fun n => n ^ c + 1 := by
  sorry

/-- **Savitch's theorem** ([AB09, Theorem 4.14]; [Sav70]): for
space-constructible `S`, nondeterministic space `S` sits inside deterministic
space `S²`.

**Proof sketch.** Let `N` decide `L` in space `c₀ · S`. Membership is
acceptance within the vertex count
(`Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound`), i.e.
reachability, in the configuration graph restricted to the window
`[-c₀·S n, c₀·S n]`, from the initial vertex to an accepting one
(`Turing.NDTM.reflTransGen_cfgStep_iff` for the dictionary) within
`V := N.configBound n (c₀·S n)` steps, where `log₂ V = O(S n)` (the
`configBound` exponent arithmetic). The deterministic decider evaluates
`reach?(u, v, i)` — is there a path of length at most `2^i` — by the midpoint
recursion: enumerate midpoints `m` over the coded vertices and recurse on
`(u, m, i - 1)` and `(m, v, i - 1)`, **reusing the space** of the first
recursive call for the second ([AB09]'s crucial point). Realized iteratively:
an explicit stack of at most `log₂ V + 1 = O(S n)` frames, each one coded
vertex pair plus a midpoint cursor of `O(S n)` bits, held on a dedicated bank
and walked with the catalog copy/compare/increment routines under the loop
combinator; one extra bank runs the vertex-adjacency test (one
transition-table application on decoded cores) and the base case. Space:
frames × frame size `= O((S n)²)`, plus `O(S n)` administration — inside
`SPACE (S·S)`'s constant absorption. The initial radius computation is the
constructibility witness, whose own space is `O(S n)`. Named fill
obligations: the frame-stack discipline (a §12 R1/R2 consumer — bank
embedding for the stack bank, seam composition per frame transition), the
midpoint enumerator, the adjacency tester, and the arithmetic packaging
`O(S²) ≤ c' · (S n · S n)`. Positivity of the target bound is automatic
(`S ≥ logSpace ≥ 1`). -/
theorem savitch (S : ℕ → ℕ) (hS : SpaceConstructible S) :
    NSPACE S ⊆ SPACE fun n => S n * S n := by
  sorry

/-- **`PSPACE = NPSPACE`** ([AB09, §4.2.1]): at the polynomial level,
Savitch's quadratic overhead is absorbed.

**Proof sketch.** `⊆` is `Complexity.PSPACE_subset_NPSPACE` (phase P4.1).
`⊇`: a member of `NPSPACE` lives in some `NSPACE (n ^ c + 1)`; route `c = 0`
into `c = 1` by the class's constant absorption — a decider within
`c₁ · (n ^ 0 + 1) = 2 · c₁` cells is a decider within `2c₁ · (n ^ 1 + 1)`
cells (bare `Complexity.NSPACE.mono` does not apply: its pointwise hypothesis
fails at `n = 0`, where `n ^ 0 + 1 = 2 > n + 1 = 1`); for `1 ≤ c`,
`Complexity.savitch` with `Complexity.spaceConstructible_poly` gives
membership in `SPACE ((n^c + 1) · (n^c + 1))`, and
`(n^c + 1)² ≤ 4 · (n^{2c} + 1)` lets `Complexity.SPACE.mono` plus the class's
constant absorption land it in `SPACE (n^{2c} + 1) ⊆ PSPACE`
(`Complexity.space_poly_subset_PSPACE`). -/
theorem PSPACE_eq_NPSPACE : PSPACE = NPSPACE := by
  sorry

end Complexity
