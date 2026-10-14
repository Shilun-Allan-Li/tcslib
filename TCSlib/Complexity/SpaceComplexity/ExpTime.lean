/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan, Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Main

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic space in exponential time, and `NL ⊆ P`

[AB09, Theorem 4.2, third inclusion]: for space-constructible `S`,
`NSPACE S ⊆ ⋃ c, DTIME (2 ^ (c · (S n + 1)))`; at `S = logSpace` this is `NL ⊆ P`, the
nondeterministic step of the p. 92 chain, and with it every nontrivial language is `NL`-hard
under polynomial-time reductions ([AB09, Exercise 4.3]). Phase P4.2 of
`AroraBarakChapters3-4Plan.md`.

These three theorems were stated in `TCSlib.Complexity.SpaceComplexity.ConfigGraph`; their
proof needs the configuration codec (`TCSlib.Complexity.SpaceComplexity.Codec`), which itself
imports that module, so they live here, after the codec, with their statements unchanged.
The simulation is the breadth-first search memory machine of
`TCSlib.Complexity.SpaceComplexity.ExpBFS`, timed by
`Complexity.LogProg.marm_dtime` (`TCSlib.Complexity.SpaceComplexity.Machines.MARMTime`).

## Main results

* `Complexity.NSPACE_subset_exp_dtime` — [AB09, Theorem 4.2, third inclusion].
* `Complexity.NL_subset_P` — the p. 92 chain's nondeterministic step.
* `Complexity.polyTimeReducible_of_mem_NL` — [AB09, Exercise 4.3]: every
  nontrivial language is `NL`-hard under polynomial-time reductions.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Theorem 4.2; §4.1.2; Exercise 4.3.)
-/

namespace Complexity

open Turing

/-- **Nondeterministic space sits inside exponential time**
([AB09, Theorem 4.2, third inclusion]): for space-constructible `S`,
`NSPACE S ⊆ ⋃ c : ℕ, DTIME (2 ^ (c · (S n + 1)))`. The union over `c` renders the
book's `2^{O(S(n))}`; the `+ 1` is a harmless normalization whose job is the
input-head absorption (`n + 2 ≤ 2 ^ (S n + 1)`, since `SpaceConstructible`
bundles `logSpace n ≤ S n`) — the displayed time bound is everywhere positive
regardless, and the `c = 0` component has exponent `0` (round-1 audit,
finding 5).

**Proof sketch.** Only the lower bound `logSpace ≤ S` of constructibility is used
(`Complexity.NSPACE_subset_exp_dtime_of_le`). Let `N` decide `L` in space `c₀ · S`. The
deterministic simulator is a register machine with a monotone memory tape
(`Complexity.LogProg.ExpBFS.A`): registers hold configuration codes of `N` at a radius `s`
(`TCSlib.Complexity.SpaceComplexity.Codec`: `O(s + log n)` bits, so below `2 ^ O(S n)`), the
memory holds visited marks. For `s = 0, 1, …` it breadth-first searches the configuration
graph at radii `s` and `s + 1` (marking the initial code, then relaxing step pairs, asked of
the logspace step-pair decider, until a round marks nothing) and counts the reachable codes;
the counts do not drop as the radius grows, and at the first `s` where they agree no branch
leaves the window, so `x ∈ L` iff a reachable code at radius `s` is accepting
(`Complexity.ExpBFS.mem_iff_of_card_eq`); agreement happens by `s = c₀ S |x|`
(`Complexity.ExpBFS.card_rset_succ_of_le`). The time is a configuration count of the compiled
machine (`Complexity.LogProg.marm_dtime`): its small tapes have `O(S n)` cells and its memory
tape, of `2 ^ O(S n)` cells, only gains `1`s, so a halting run sees at most
`2 ^ O(S n) · (2 ^ O(S n))²` configurations; this is `2 ^ (c (S n + 1))`. -/
theorem NSPACE_subset_exp_dtime (S : ℕ → ℕ) (hS : SpaceConstructible S) :
    NSPACE S ⊆ ⋃ c : ℕ, DTIME fun n => 2 ^ (c * (S n + 1)) :=
  NSPACE_subset_exp_dtime_of_le S hS.1

/-- **`NL ⊆ P`** — the nondeterministic step of the p. 92 chain
([AB09, §4.1.2 with Exercise 4.3's premise]). At `S = logSpace` the vertex
count is polynomial, so the breadth-first search runs in polynomial time.

**Proof sketch.** Instantiate `Complexity.NSPACE_subset_exp_dtime` at `logSpace`
(`spaceConstructible_logSpace`): a language of `NL` is in `DTIME (2 ^ (c (logSpace n + 1)))`
for some `c`, and `2 ^ (c (⌊log₂ n⌋ + 2)) = 2 ^ (2c) (2 ^ ⌊log₂ n⌋) ^ c ≤ 2 ^ (2c) (n + 1) ^ c
≤ 2 ^ (3c) (n ^ c + 1)` (`succ_pow_le`), a polynomial bound (`mem_P_of_dtime_le`). -/
theorem NL_subset_P : NL ⊆ P := by
  intro L hL
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp
    (NSPACE_subset_exp_dtime logSpace spaceConstructible_logSpace hL)
  refine mem_P_of_dtime_le hc (2 ^ (3 * c)) c fun n => ?_
  have hlog : 2 ^ Nat.log 2 n ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (Nat.pow_log_le_self 2 hn.ne').trans (Nat.le_succ n)
  calc
    2 ^ (c * (logSpace n + 1)) = 2 ^ (2 * c) * (2 ^ Nat.log 2 n) ^ c := by
      rw [← pow_mul, ← pow_add]
      congr 1
      simp only [logSpace]
      ring
    _ ≤ 2 ^ (2 * c) * (n + 1) ^ c :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlog c)
    _ ≤ 2 ^ (2 * c) * (2 ^ c * (n ^ c + 1)) :=
      Nat.mul_le_mul_left _ (succ_pow_le n c)
    _ = 2 ^ (3 * c) * (n ^ c + 1) := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega

/-- **Polynomial-time reductions are too coarse below `P`**
([AB09, Exercise 4.3]): every language that is neither empty nor full is
`NL`-hard under polynomial-time Karp reductions — so `NL`-completeness is
only meaningful for the logspace reductions of phase P4.4
([AB09, Definition 4.16]; the exercise's intended moral, recorded in its
docstring rather than left implicit). **Corrects the exercise's printed
wording**: p. 93 says "complete for `NL`" for an arbitrary nontrivial target,
which is false without target membership in `NL` (an undecidable nontrivial
target defeats completeness); only hardness is claimed here, and
completeness additionally requires `L ∈ NL` (round-1 audit, finding 2).

**Proof sketch.** Fix witnesses `y₀ ∈ L` and `z₀ ∉ L` (classical choice). For
`L' ∈ NL`, `Complexity.NL_subset_P` gives a polynomial-time decider of `L'`;
the reduction `f x := if x ∈ L' then y₀ else z₀` is polynomial-time
computable by the conditional catalog (`Complexity.polyTimeComputable_ite`
over the decider with two `Complexity.polyTimeComputable_const` branches),
and `x ∈ L' ↔ f x ∈ L` holds by the choice of witnesses. It makes no decision procedure for
`L`. -/
theorem polyTimeReducible_of_mem_NL (L : Language Bool) (hy : ∃ y, y ∈ L)
    (hz : ∃ z, z ∉ L) {L' : Language Bool} (hL' : L' ∈ NL) : L' ≤ₚ L := by
  classical
  obtain ⟨y, hy⟩ := hy
  obtain ⟨z, hz⟩ := hz
  obtain ⟨C, d, M, hM⟩ := mem_P_iff.mp (NL_subset_P hL')
  have test : PolyTimeComputable (fun x => [MultiTapeTM.indicator L' x]) :=
    ⟨M, C, d, hM⟩
  refine ⟨fun x => if MultiTapeTM.indicator L' x then y else z,
    polyTimeComputable_ite test (polyTimeComputable_const y) (polyTimeComputable_const z), ?_⟩
  intro x
  by_cases hx : x ∈ L' <;> simp [MultiTapeTM.indicator, hx, hy, hz]

end Complexity
