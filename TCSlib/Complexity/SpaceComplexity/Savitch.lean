/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Correct
import TCSlib.Complexity.SpaceComplexity.SavitchARM.Deepen

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Savitch's theorem

[AB09, Theorem 4.14] ([Sav70]): for space-constructible `S`,
`NSPACE(S(n)) ⊆ SPACE(S(n)²)` — nondeterministic space costs only a quadratic
deterministic overhead, via Savitch's midpoint search `reach?(u, v, i)` over the
machine's configurations, here realized by a register machine. The
corollary `PSPACE = NPSPACE` ([AB09, §4.2.1]) closes the polynomial level.

**Status.** Both results are proved. `Complexity.savitch_of_logSpace_le` proves the inclusion
for every space bound `S ≥ logSpace`, and `Complexity.savitch` follows, since
space-constructibility includes `logSpace ≤ S` and nothing else of it is used: the deepening
register machine of
`TCSlib.Complexity.SpaceComplexity.SavitchARM.Deepen` decides `L` with registers of
`O((S n)²)` digits (`Complexity.LogProg.SavitchARM.deepen_contract`), and
`Complexity.LogProg.arm_decides_SPACE` turns it into a deterministic decider in space
`O(S · S)`. `Complexity.PSPACE_eq_NPSPACE` is proved directly, at the polynomial level, by the
Savitch register machine of `TCSlib.Complexity.SpaceComplexity.SavitchARM`
(`Complexity.NPSPACE_subset_PSPACE`). The polynomial bounds' constructibility,
`Complexity.spaceConstructible_poly`, is in `TCSlib.Complexity.SpaceComplexity.Constructible`.

## Design

* **The positive-bound convention is respected without side conditions**:
  `Complexity.SpaceConstructible` bundles `logSpace n ≤ S n`, so `S` and
  `S · S` are everywhere positive and the zero-bound convention
  (`TCSlib.Complexity.SpaceComplexity.ZeroSpace`) imposes no extra hypothesis.
* **The radius is found by iterative deepening, not computed**: instead of computing
  `S(|x|)` from a constructibility witness, the machine runs Savitch's midpoint search at
  radius `s = 1, 2, …` ([Sip13, §8.1, proof of Theorem 8.5]). At each radius it first asks
  whether a configuration with a work head on the window's edge is reachable; if none is,
  membership is reachability at that radius
  (`Complexity.LogProg.SavitchARM.mem_iff_reach_of_noEdge`), and beyond the space bound none is
  (`Complexity.LogProg.SavitchARM.noEdge_of_lt`), so for a machine deciding in space `c · S`
  the search stops by radius `c · S(|x|) + 1`.
* **The recursion is realized by a register machine**: the midpoint search is the Savitch
  register machine (`Complexity.LogProg.SavitchARM.A`), whose explicit stack keeps every
  register within `w · w` binary digits for a code width `w = O(S n)`; the deepening machine
  holds it twice as a block of its own table (`Complexity.LogProg.Ins.embed`).

## Main definitions

None: the module states theorems only.

## Main results

* `Complexity.savitch_of_logSpace_le` — [AB09, Theorem 4.14] for every `S ≥ logSpace`.
* `Complexity.savitch` — [AB09, Theorem 4.14].
* `Complexity.PSPACE_eq_NPSPACE` — [AB09, §4.2.1].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14; §4.1.2.)
* [Sav70] W. J. Savitch, *Relationships between nondeterministic and
  deterministic tape complexities*, JCSS 4(2), 1970. (Cited through [AB09].)
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage Learning,
  2013. (§8.1, the proof of Theorem 8.5: the space bound found by trying `1, 2, …`.)
-/

namespace Complexity

open Turing

/-- **Savitch's theorem for every bound `S ≥ logSpace`** ([AB09, Theorem 4.14]; [Sav70]):
nondeterministic space `S` sits inside deterministic space `S²` whenever `S ≥ logSpace`; no
constructibility is needed, since the space bound is found by trying `1, 2, …` ([Sip13, §8.1,
proof of Theorem 8.5]).

**Proof sketch.** Let `N` decide `L` in space `c · S`. The deepening machine
(`Complexity.LogProg.SavitchARM.deepen_contract`) answers `x ∈ L` with logspace deciders and
registers of at most `C (c · S |x| + logSpace |x| + 1)²` binary digits. Since
`logSpace ≤ S` and `S ≥ 1`, this is at most `C (c + 2)² · (S |x| · S |x|)`, and
`Complexity.LogProg.arm_decides_SPACE` gives `L ∈ SPACE (S · S)`. -/
theorem savitch_of_logSpace_le (S : ℕ → ℕ) (hS : ∀ n, logSpace n ≤ S n) :
    NSPACE S ⊆ SPACE fun n => S n * S n := by
  rintro L ⟨c, N, hN⟩
  obtain ⟨m, d, Λ, _, _, D, l₀, As, hAs, C, hcorr⟩ := LogProg.SavitchARM.deepen_contract hN
  have hS1 : ∀ n, 1 ≤ S n := fun n => le_trans (by rw [logSpace_eq]; omega) (hS n)
  refine LogProg.arm_decides_SPACE D l₀ As hAs (fun n => S n * S n)
    (fun n => (hS n).trans (Nat.le_mul_of_pos_right _ (hS1 n))) (C * (c + 2) ^ 2) (fun x => ?_)
  refine (hcorr x).mono fun a ha => ⟨ha.1, fun r => (ha.2 r).trans ?_⟩
  have h1 : c * S x.length + logSpace x.length + 1 ≤ (c + 2) * S x.length := by
    have := hS x.length; have := hS1 x.length; nlinarith
  calc C * (c * S x.length + logSpace x.length + 1) ^ 2
      ≤ C * ((c + 2) * S x.length) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)
    _ = C * (c + 2) ^ 2 * (S x.length * S x.length) := by ring

/-- **Savitch's theorem** ([AB09, Theorem 4.14]; [Sav70]): for
space-constructible `S`, nondeterministic space `S` sits inside deterministic
space `S²`.

**Proof sketch.** Space-constructibility includes `logSpace ≤ S`, so this is
`Complexity.savitch_of_logSpace_le`. There, the radius `S(|x|)` is never computed: the
deterministic machine runs Savitch's midpoint search ([AB09]'s `reach?(u, v, i)`, reusing the
space of the first recursive call for the second) over the configuration codes at radius
`s = 1, 2, …`, first asking whether a configuration with a work head on the window's edge `±s`
is reachable. If one is, the space bound exceeds `s` and it tries `s + 1`; if none is, every
run stays inside the window, so membership is reachability of an accepting code at radius `s`,
which it decides by the same search. The search stops by `s = c · S |x| + 1`, the code width is
`O(S |x|)`, and the search's stack keeps every register within its square, so the space is
`O((S |x|)²)`. -/
theorem savitch (S : ℕ → ℕ) (hS : SpaceConstructible S) :
    NSPACE S ⊆ SPACE fun n => S n * S n :=
  savitch_of_logSpace_le S hS.1

/-- **`PSPACE = NPSPACE`** ([AB09, §4.2.1]; [AB09, Theorem 4.14] at polynomial
space bounds): at the polynomial level, Savitch's quadratic overhead is absorbed.

**Proof sketch.** `⊆` is `Complexity.PSPACE_subset_NPSPACE`. `⊇` is
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
