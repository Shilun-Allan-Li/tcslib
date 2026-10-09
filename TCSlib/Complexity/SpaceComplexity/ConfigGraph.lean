/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Logic.Relation
import TCSlib.Complexity.SpaceComplexity.NSPACE
import TCSlib.Complexity.SpaceComplexity.SpaceClasses
import TCSlib.Complexity.SpaceComplexity.ConfigCount
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.ClassNP.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Configuration graphs of nondeterministic machines

[AB09, §4.1.1]: the configuration graph `G_{M,x}` of a machine on an input —
vertices the configurations, edges the one-step transitions (out-degree at most
two for a binary-choice NDTM) — together with the counting half of Claim 4.4(1)
for nondeterministic branches, the exponential-time simulation
([AB09, Theorem 4.2, third inclusion]), `NL ⊆ P`, and the coarseness of
polynomial-time reductions below `P` ([AB09, Exercise 4.3]). This is phase P4.2
of `AroraBarakChapters3-4Plan.md`; Savitch's theorem, the other consumer of
this layer, is `TCSlib.Complexity.SpaceComplexity.Savitch`.

**Status: statement skeleton (phase P4.2).** Definitions are real; every
contract is sorried with a sketch naming its fill obligations.

## Design

* **The vertex is a core plus a bounded output summary.** The received
  deterministic counting layer (`Turing.MultiTapeTM.ConfigCount`) counts
  *cores* — configurations without their output tapes — which is sound for
  halting-time bounds because output is write-only. For *acceptance* along a
  branch it is **not** sufficient by itself: acceptance means output exactly
  `[true]` at a halted configuration, and splicing out a cycle between equal
  cores could delete the branch's one emission (the P0 reception audit's
  fitness note, `audits/ch34-p0-findings.md` §7, anticipated exactly this). The
  vertex therefore carries `Turing.OutSummary` — the three-valued quotient of
  the output by its relation to `[true]`: still empty, exactly `[true]`, or
  irrecoverably dead — which is compatible with the append-only output
  discipline and multiplies the core count by three
  (`Turing.FinNDTM.configBound`).
* **The graph is the step relation, not a finite object**: `Turing.NDTM.CfgStep`
  is a relation on configurations, with `Relation.ReflTransGen` as
  reachability; the finite counting enters only through the (sorried) bounds.
  Efficient vertex *encoding* reuses `Turing.MultiTapeTM.ConfigCount.coreCode`;
  the adjacency CNF of Claim 4.4(2) is deliberately phase P4.3.
* **Facade wiring**: root-wired while the P4.1 gate was live; since that
  gate closed (round 1, PASS), the `SpaceComplexity.lean` facade carries this
  module and `Savitch`.

## Main definitions

* `Turing.OutSummary`, `Turing.outSummary` — the three-valued output summary.
* `Turing.NDTM.coreSum` — the configuration-graph vertex: core plus summary.
* `Turing.NDTM.CfgStep` — the edge relation (one `stepWith`, either choice).
  [AB09, §4.1.1: out-degree at most two]
* `Turing.FinNDTM.configBound` — the vertex count at window radius `s`:
  three times the deterministic `configBound` formula. [AB09, Claim 4.4(1)]

## Main results (all sorried; phase-P4.2 statements)

* `Turing.NDTM.reflTransGen_cfgStep_iff` — reachability is the choice-word run.
* `Turing.NDTM.coreSum_stepWith` — a step's vertex depends only on the vertex.
* `Turing.FinNDTM.acceptsWithin_of_spaceUsedWith_le` — Claim 4.4(1),
  acceptance form: a space-`s` accepting branch shortens to the vertex count.
* `Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound` — the
  packaged interface the simulations consume.
* `Complexity.NSPACE_subset_exp_dtime` — [AB09, Theorem 4.2, third inclusion].
* `Complexity.NL_subset_P` — the p. 92 chain's nondeterministic step.
* `Complexity.polyTimeReducible_of_mem_NL` — [AB09, Exercise 4.3]: every
  nontrivial language is `NL`-hard under polynomial-time reductions.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4, Theorem 4.2;
  §4.1.2; Exercise 4.3.)
-/

namespace Turing

variable {k : ℕ} {S : Type} {x : List Bool}

/-- The three-valued summary of an append-only output word relative to the
acceptance target `[true]`: still empty, exactly `[true]`, or dead — no
further appending can reach `[true]` from a dead output. The quotient the
configuration-graph vertex carries alongside the core (see the module
docstring for why the core alone cannot certify acceptance). -/
inductive OutSummary where
  /-- nothing emitted yet -/
  | empty
  /-- the output is exactly `[true]` -/
  | accept
  /-- the output can no longer become `[true]` -/
  | dead
deriving DecidableEq

/-- The summary of an output word: `[]` is `empty`, `[true]` is `accept`,
everything else is `dead`. Compatible with appending — the summary of
`out ++ e` is a function of the summary of `out` and `e` alone, which is what
makes the vertex sound for splicing arguments. -/
def outSummary : List Bool → OutSummary
  | [] => .empty
  | [true] => .accept
  | _ => .dead

namespace NDTM

/-- The configuration-graph **vertex** of a configuration: its core (state,
input position, work tapes, work heads — `Turing.MultiTapeTM.ConfigCount.core`)
together with the output summary. Two configurations with equal vertices have
equal futures up to output-suffix equality, which is exactly what acceptance
needs. [AB09, §4.1.1] -/
def coreSum (c : Cfg k Bool S x) :
    (Option S × Fin (x.length + 2) × (Fin k → ℤ → Option Bool) × (Fin k → ℤ)) ×
      OutSummary :=
  (MultiTapeTM.ConfigCount.core c, outSummary c.output)

/-- The configuration-graph **edge relation** of [AB09, §4.1.1]: `c` steps to
`c'` under some choice bit. A binary-choice NDTM gives out-degree at most two;
a halted configuration self-loops (`Turing.NDTM.stepWith_of_halt`). -/
def CfgStep (tm : NDTM k Bool S) (c c' : Cfg k Bool S x) : Prop :=
  ∃ b : Bool, tm.stepWith b c = c'

/-- **Reachability in the configuration graph is the choice-word run**
(spec, fill pending — phase P4.2): `c'` is `Relation.ReflTransGen`-reachable
from `c` along `Turing.NDTM.CfgStep` iff some choice word runs `c` to `c'`.
This is the dictionary between [AB09]'s graph language and the campaign's
`runWith` semantics.

**Proof sketch.** Forward: induction on the reflexive-transitive chain,
appending the step's choice bit (`Turing.NDTM.runWith_append` at a singleton).
Backward: induction on the word, `Relation.ReflTransGen.head` at each consumed
bit (`Turing.NDTM.runWith_cons`). -/
theorem reflTransGen_cfgStep_iff (tm : NDTM k Bool S) (c c' : Cfg k Bool S x) :
    Relation.ReflTransGen (tm.CfgStep) c c' ↔ ∃ w : List Bool, tm.runWith w c = c' := by
  sorry

/-- **A step's vertex depends only on the vertex** (spec, fill pending — phase
P4.2; the nondeterministic, summary-carrying analogue of
`Turing.MultiTapeTM.ConfigCount.core_step`): configurations with equal
`coreSum` have equal `coreSum` after one `stepWith` under the same choice bit.

**Proof sketch.** The action is selected from the state and the scanned
symbols, all read off the core (as in `core_step`: `Cfg.inputSymbol` and
`Cfg.workTapeSymbols` are core-determined), so the two steps apply the same
action to cores that agree; the new output is the old output appended by the
action's emission, and `Turing.outSummary` of an append is a function of the
old summary and the emission (case analysis on the three summary values and
the optional emitted bit — the compatibility fact of the summary quotient). -/
theorem coreSum_stepWith (tm : NDTM k Bool S) (b : Bool) {c d : Cfg k Bool S x}
    (h : coreSum c = coreSum d) :
    coreSum (tm.stepWith b c) = coreSum (tm.stepWith b d) := by
  sorry

end NDTM

namespace FinNDTM

/-- The configuration-graph **vertex count** of `N` on inputs of length `n`
with window radius `s`: three (the output summaries) times the deterministic
core-code count of `Turing.FinTM.configBound` —
`3 · (|Q| + 1) · (n + 2) · 3^{k(2s+1)} · (2s+1)^k`. [AB09, Claim 4.4(1), with
the campaign's explicit constants] -/
def configBound (N : FinNDTM Bool) (n s : ℕ) : ℕ :=
  3 * ((Fintype.card N.State + 1) * (n + 2) * 3 ^ (N.k * (2 * s + 1)) *
    (2 * s + 1) ^ N.k)

/-- **Claim 4.4(1), acceptance form** (spec, fill pending — phase P4.2): an
accepting branch of length `T` whose sibling branches of length `T` all stay
within `s` visited work cells shortens to an accepting branch of length the
vertex count: `AcceptsWithin x (N.configBound x.length s)`.

**Proof sketch.** Fix the accepting word `w`, `|w| = T`. Along its run every
head and nonblank cell stays in the window `[-s, s]` (the branch-space
hypothesis at `w` itself, through the interval structure of visited sets —
the `Turing.NDTM.visitedWith` analogues of `abs_pos_lt_card_visited` and
`mem_visited_of_ne_none`, named fill obligations). If two prefixes of the run
share a `Turing.NDTM.coreSum`, splice out the cycle: by
`Turing.NDTM.coreSum_stepWith` (iterated along the remaining choice bits) the
spliced run replays the suffix's vertices, so it halts with the same summary —
and `accept` as a final summary is acceptance, outputs being read only through
the summary. Iterate until all vertices along the branch are distinct; their
codes (`Turing.MultiTapeTM.ConfigCount.coreCode` within the window, paired
with the summary) are injective (`coreCode_inj`), so the branch length is at
most `N.configBound x.length s`, and the shortened word pads back up to the
exact count (`Turing.FinNDTM.AcceptsWithin.mono` — `AcceptsWithin` demands
exact word length); if the original `T` is already smaller, pad directly
instead (the same `mono`). In either case it is the **accepting branch**
that stays halted under padding (`Turing.NDTM.runWith_of_halt`): the
statement carries no sibling-halting hypothesis and needs none (round-1
audit, finding 1). -/
theorem acceptsWithin_of_spaceUsedWith_le (N : FinNDTM Bool) {x : List Bool}
    {T s : ℕ} (hacc : N.AcceptsWithin x T)
    (hs : ∀ w : List Bool, w.length = T →
      N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ s) :
    N.AcceptsWithin x (N.configBound x.length s) := by
  sorry

/-- **The packaged graph interface** (spec, fill pending — phase P4.2): a
machine deciding `L` in space `s` accepts exactly the members within the
vertex-count budget. This is the single statement the exponential-time
simulation ([AB09, Theorem 4.2]), `Complexity.NL_subset_P`, and Savitch's
midpoint recursion all consume.

**Proof sketch.** Forward: `Turing.FinNDTM.DecidesInSpace` supplies the budget
`T` with all-branch halting, the branch-space bound, and the acceptance
equivalence; `Turing.FinNDTM.acceptsWithin_of_spaceUsedWith_le` shortens to
the vertex count. Backward: given an accepting branch at the vertex-count
budget, compare with `T`: if the budget exceeds `T`, the branch's `T`-prefix
is already halted (`Turing.NDTM.HaltsWithin`) with the run frozen
(`Turing.NDTM.runWith_of_halt`), so the prefix accepts and membership follows
from the equivalence at `T`; otherwise pad
(`Turing.FinNDTM.AcceptsWithin.mono`). -/
theorem DecidesInSpace.mem_iff_acceptsWithin_configBound {N : FinNDTM Bool}
    {L : Language Bool} {s : ℕ → ℕ} (h : N.DecidesInSpace L s) (x : List Bool) :
    x ∈ L ↔ N.AcceptsWithin x (N.configBound x.length (s x.length)) := by
  sorry

end FinNDTM

end Turing

namespace Complexity

open Turing

/-- **Nondeterministic space sits inside exponential time**
([AB09, Theorem 4.2, third inclusion]): for space-constructible `S`,
`NSPACE S ⊆ ⋃ c, DTIME (2 ^ (c · (S n + 1)))`. The union over `c` renders the
book's `2^{O(S(n))}`; the `+ 1` is a harmless normalization whose job is the
input-head absorption (`n + 2 ≤ 2 ^ (S n + 1)`, since `SpaceConstructible`
bundles `logSpace n ≤ S n`) — the displayed time bound is everywhere positive
regardless, and the `c = 0` component has exponent `0` (round-1 audit,
finding 5).

**Proof sketch.** Let `N` decide `L` in space `c₀ · s`. The deterministic
simulator, on input `x`: (i) computes the window radius `c₀ · S |x|` from the
constructibility witness; (ii) runs a breadth-first search over the
configuration graph on the coded vertices
(`Turing.MultiTapeTM.ConfigCount.coreCode` plus the summary): the vertex count
is `N.configBound |x| (c₀·S |x|) ≤ 2^{O(S |x|)}` (the exponent arithmetic of
the received `configBound_logSpace_le`, generalized from `logSpace` to `S`),
each vertex has out-degree two computed by one transition-table application,
and the search maintains a visited table of coded vertices — the catalog
copy/compare/increment routines and the loop combinator are the engine
(`machine-library-design.md` §12 R3, `Build/Catalog.lean`); (iii) accepts iff
a vertex with halted state and `accept` summary is reached, which is
membership by
`Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound` and
`Turing.NDTM.reflTransGen_cfgStep_iff`. Total time: vertices × edges × table
operations, `2^{O(S n)}`, normalized into the stated exponent with the
`n + 2 ≤ 2^{S n + 1}` absorption. Fill obligations, named: the BFS controller
(continuation budget anticipated), the vertex codec machine, the
bound-generalized `configBound` arithmetic. -/
theorem NSPACE_subset_exp_dtime (S : ℕ → ℕ) (hS : SpaceConstructible S) :
    NSPACE S ⊆ ⋃ c : ℕ, DTIME fun n => 2 ^ (c * (S n + 1)) := by
  sorry

/-- **`NL ⊆ P`** — the nondeterministic step of the p. 92 chain
([AB09, §4.1.2 with Exercise 4.3's premise]). At `S = logSpace` the vertex
count is polynomial, so the breadth-first search runs in polynomial time.

**Proof sketch.** Instantiate the simulator of
`Complexity.NSPACE_subset_exp_dtime` at `logSpace`: the vertex count
`N.configBound n (c₀ · logSpace n)` is bounded by a fixed polynomial in `n`
(the received `Turing.FinTM.configBound_logSpace_le` arithmetic, times three),
so the BFS with its table fits in `DTIME (n^d + 1)` for a fixed `d` —
with count arithmetic analogous to the received
`Complexity.LOGSPACE_subset_P` — whose own proof keeps the original machine
and bounds its halting time through `ComputesInSpace`, constructing no
search or visited table (round-1 audit, finding 4). Continuation budget
anticipated: the external prior art's `NL ⊆ P` was a full submission on its
own ([Bon26] context in `machine-library-design.md` §12 — reachability-table
construction; design only, nothing ported). -/
theorem NL_subset_P : NL ⊆ P := by
  sorry

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
and `x ∈ L' ↔ f x ∈ L` holds by the choice of witnesses. -/
theorem polyTimeReducible_of_mem_NL (L : Language Bool) (hy : ∃ y, y ∈ L)
    (hz : ∃ z, z ∉ L) {L' : Language Bool} (hL' : L' ∈ NL) : L' ≤ₚ L := by
  sorry

end Complexity
