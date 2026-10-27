/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Correct

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

**Status: partly filled (phase P4.2).** `Complexity.PSPACE_eq_NPSPACE` is
proved, directly at the polynomial level, by the Savitch register machine of
`TCSlib.Complexity.SpaceComplexity.SavitchARM` (`Complexity.NPSPACE_subset_PSPACE`);
`Complexity.savitch` (general space-constructible `S`) remains sorried with a sketch
naming its fill obligations. The polynomial bounds' constructibility,
`Complexity.spaceConstructible_poly`, is in `TCSlib.Complexity.SpaceComplexity.Constructible`.
The `SpaceComplexity.lean` facade has carried this module since the P4.1 gate closed
(root-wired while that gate was live).

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

## Main results

* `Complexity.savitch` — [AB09, Theorem 4.14]. (Sorried.)
* `Complexity.PSPACE_eq_NPSPACE` — [AB09, §4.2.1]. (Proved.)

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14; §4.1.2.)
* [Sav70] W. J. Savitch, *Relationships between nondeterministic and
  deterministic tape complexities*, JCSS 4(2), 1970. (Cited through [AB09];
  no external text is required for this audit.)
-/

namespace Complexity

open Turing

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

/-- **`PSPACE = NPSPACE`** ([AB09, §4.2.1]; [AB09, Theorem 4.14] at polynomial
space bounds): at the polynomial level, Savitch's quadratic overhead is absorbed.

**Proof sketch.** `⊆` is `Complexity.PSPACE_subset_NPSPACE` (phase P4.1). `⊇` is
`Complexity.NPSPACE_subset_PSPACE`, proved directly rather than through
`Complexity.savitch`: for `N` deciding `L` in space `c (n ^ k + 1)`, take the radius
`s = (n + 2) ^ E` and the code width `w = (n + 2) ^ (2E)` (`E` a constant of `N`, `k`, `c`),
so that the configuration codes of `TCSlib.Complexity.SpaceComplexity.Codec` lie below
`2 ^ w` and the configuration count is at most `2 ^ w`; then `x ∈ L` iff some initial code
reaches some accepting code by the midpoint predicate `REACH(u, v, w)` (paths of length at
most `2 ^ w`, every midpoint a code below `2 ^ w`). The Savitch register machine
(`Complexity.LogProg.SavitchARM.A`) computes `s`, `w`, `2 ^ w` by counting loops and
evaluates `REACH` by the midpoint recursion, **reusing the space** of the first recursive
call for the second ([AB09]'s crucial point) through an explicit stack: saved endpoints as
`w`-bit digits of one register, phase bits as binary digits of another, so every register
holds at most `w · w` bits. Its deciders (input length and the initial, accepting and step
code languages) are logspace, and `Complexity.LogProg.arm_decides_pspace_val` turns the
machine into a polynomial-space decider. -/
theorem PSPACE_eq_NPSPACE : PSPACE = NPSPACE :=
  Set.Subset.antisymm PSPACE_subset_NPSPACE NPSPACE_subset_PSPACE

end Complexity
