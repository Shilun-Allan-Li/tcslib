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

**Status: graph lemmas proved (phase P4.2, batch S1a).** The four graph
contracts are proved; the three class results remain sorried for S1b.

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
  reachability; the finite counting enters only through the configuration-count
  bounds (`acceptsWithin_of_spaceUsedWith_le`, proved).
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

## Main results (graph lemmas proved; three class results sorried)

* `Turing.NDTM.reflTransGen_cfgStep_iff` — reachability is the choice-word run.
* `Turing.NDTM.coreSum_stepWith` — a step's vertex depends only on the vertex.
* `Turing.FinNDTM.acceptsWithin_of_spaceUsedWith_le` — Claim 4.4(1),
  acceptance form: a space-`s` accepting branch shortens to the vertex count.
* `Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound` — the
  packaged interface the simulations consume.
* `Turing.outSummary_eq_accept_iff` — the summary recognizes exactly `[true]`.
* `Turing.outSummary_append_congr` — a common output suffix preserves summary equality.
* `Turing.NDTM.coreSum_runWith` — a common choice word preserves vertex equality.
* `Turing.FinNDTM.not_acceptsWithin_zero` — acceptance requires a transition.
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

/-- An output summary accepts exactly the singleton true output. [AB09, §4.1.1]

**Proof sketch.** Inspect the empty, singleton, and longer output words. -/
theorem outSummary_eq_accept_iff (u : List Bool) : outSummary u = .accept ↔ u = [true] := by
  cases u with
  | nil => simp [outSummary]
  | cons a u => cases u <;> cases a <;> simp [outSummary]

/-- Equal summaries remain equal after appending a common output suffix.
[AB09, §4.1.1]

**Proof sketch.** An empty prefix contributes nothing, an accepting prefix
survives only an empty suffix, and a dead prefix stays dead. -/
theorem outSummary_append_congr {u v : List Bool} (h : outSummary u = outSummary v)
    (e : List Bool) : outSummary (u ++ e) = outSummary (v ++ e) := by
  have table (a : List Bool) : outSummary (a ++ e) =
      match outSummary a with
      | .empty => outSummary e
      | .accept => if e = [] then .accept else .dead
      | .dead => .dead := by
    cases a with
    | nil => rfl
    | cons b a => cases a <;> cases b <;> cases e <;> simp [outSummary]
  rw [table, table, h]

/-- Heads and all nonblank work cells lie in the finite coding window. -/
private def InWindow (s : ℕ) (c : Cfg k Bool S x) : Prop :=
  ∀ i, |c.workTapePos i| ≤ s ∧ ∀ z, c.workTapes i z ≠ none → |z| ≤ s

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
(proved — phase P4.2): `c'` is `Relation.ReflTransGen`-reachable
from `c` along `Turing.NDTM.CfgStep` iff some choice word runs `c` to `c'`.
This is the dictionary between [AB09]'s graph language and the campaign's
`runWith` semantics.

**Proof sketch.** Forward: induction on the reflexive-transitive chain,
appending the step's choice bit (`Turing.NDTM.runWith_append` at a singleton).
Backward: induction on the word, `Relation.ReflTransGen.head` at each consumed
bit (`Turing.NDTM.runWith_cons`). -/
theorem reflTransGen_cfgStep_iff (tm : NDTM k Bool S) (c c' : Cfg k Bool S x) :
    Relation.ReflTransGen (tm.CfgStep) c c' ↔ ∃ w : List Bool, tm.runWith w c = c' := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl⟩
    | @tail d e _ edge ih =>
      obtain ⟨w, rfl⟩ := ih
      obtain ⟨b, rfl⟩ := edge
      exact ⟨w ++ [b], by rw [runWith_append, runWith_cons, runWith_nil]⟩
  · rintro ⟨w, rfl⟩
    induction w generalizing c with
    | nil => exact Relation.ReflTransGen.refl
    | cons b w ih => exact Relation.ReflTransGen.head ⟨b, rfl⟩ (ih _)

/-- The emitted symbol is determined by the core, independently of the output history.

**Proof sketch.** Destructure the configurations and identify their four core fields;
the transition reads precisely those fields. -/
private theorem outputSymbol_congr (M : MultiTapeTM k Bool S) {c d : Cfg k Bool S x}
    (h : MultiTapeTM.ConfigCount.core c = MultiTapeTM.ConfigCount.core d) :
    M.outputSymbol c = M.outputSymbol d := by
  cases c
  cases d
  simp only [MultiTapeTM.ConfigCount.core, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  rfl

/-- **A step's vertex depends only on the vertex** (proved — phase
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
  change (MultiTapeTM.ConfigCount.core _, outSummary _) =
    (MultiTapeTM.ConfigCount.core _, outSummary _)
  have hc := congrArg Prod.fst h
  have ho := congrArg Prod.snd h
  rw [stepWith_eq_fixChoice_step, stepWith_eq_fixChoice_step]
  apply Prod.ext (MultiTapeTM.ConfigCount.core_step _ hc)
  rw [MultiTapeTM.step_output, MultiTapeTM.step_output, outputSymbol_congr _ hc]
  exact outSummary_append_congr ho _

/-- A common choice word preserves equality of configuration-graph vertices.
[AB09, §4.1.1]

**Proof sketch.** Induct on the word and apply the one-step congruence. -/
theorem coreSum_runWith (tm : NDTM k Bool S) (w : List Bool)
    {c d : Cfg k Bool S x} (h : coreSum c = coreSum d) :
    coreSum (tm.runWith w c) = coreSum (tm.runWith w d) := by
  induction w generalizing c d with
  | nil => exact h
  | cons b w ih => exact ih (coreSum_stepWith tm b h)

/-- Successive choice prefixes either leave the configuration fixed or apply one action.

**Proof sketch.** Append the optional next choice bit. If it exists, use its
deterministic slice; a halted slice is the identity. -/
private theorem take_succ_action (tm : NDTM k Bool S) (w : List Bool)
    (c : Cfg k Bool S x) (j : ℕ) :
    tm.runWith (w.take (j + 1)) c = tm.runWith (w.take j) c ∨
      ∃ a : Action k Bool S,
        tm.runWith (w.take (j + 1)) c = a.apply (tm.runWith (w.take j) c) := by
  rw [List.take_succ, runWith_append]
  cases w[j]? with
  | none => exact Or.inl rfl
  | some b =>
    simp only [Option.toList_some, runWith_cons, runWith_nil, stepWith_eq_fixChoice_step]
    unfold MultiTapeTM.step
    cases (tm.runWith (w.take j) c).state with
    | none => exact Or.inl rfl
    | some q => exact Or.inr ⟨_, rfl⟩

/-- A position visited from initialization has absolute value below the visited-set size.

**Proof sketch.** Instantiate the shared unit-step image bound with the prefix runs;
`take_succ_action` and the action head-motion bound supply unit steps. -/
private theorem abs_lt_card_visitedWith (tm : NDTM k Bool S) (w : List Bool)
    (i : Fin k) {z : ℤ} (hz : z ∈ tm.visitedWith w (tm.initCfg x) i) :
    |z| < (tm.visitedWith w (tm.initCfg x) i).card := by
  apply MultiTapeTM.ConfigCount.abs_lt_card_image_of_unitSteps
    (fun j => (tm.runWith (w.take j) (tm.initCfg x)).workTapePos i) (by simp) _ w.length hz
  intro j
  dsimp only
  rcases take_succ_action tm w (tm.initCfg x) j with same | ⟨a, step⟩
  · rw [same]; simp
  · rw [step]; exact workTapePos_apply_le a _ i

/-- Every nonblank cell of a choice-word run from initialization has been visited.

**Proof sketch.** Instantiate the shared blank-tape action-sequence lemma with
prefix runs and their single `take_succ_action` decomposition. -/
private theorem mem_visitedWith_of_ne_none (tm : NDTM k Bool S) (w : List Bool)
    (i : Fin k) (z : ℤ) (hz : (tm.runWith w (tm.initCfg x)).workTapes i z ≠ none) :
    z ∈ tm.visitedWith w (tm.initCfg x) i := by
  exact MultiTapeTM.ConfigCount.mem_image_workTapePos_of_ne_none
    (fun j => tm.runWith (w.take j) (tm.initCfg x)) (by simp)
    (take_succ_action tm w (tm.initCfg x)) w.length i z
    (by simpa only [List.take_length] using hz)

/-- Taking a choice prefix only removes visited positions.

**Proof sketch.** Each prefix of the shortened word is the same prefix of the
original word, with an index no larger than either word's length. -/
private theorem visitedWith_take_subset (tm : NDTM k Bool S) (w : List Bool)
    (c : Cfg k Bool S x) (j : ℕ) (i : Fin k) :
    tm.visitedWith (w.take j) c i ⊆ tm.visitedWith w c i := by
  apply Finset.image_subset_iff.mpr
  intro n hn
  have hn' : n ≤ min j w.length := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  apply Finset.mem_image.mpr
  refine ⟨n, Finset.mem_range.mpr (by omega), ?_⟩
  rw [List.take_take, Nat.min_eq_left (by omega : n ≤ j)]

/-- A space-bounded branch has every prefix in its coding window.

**Proof sketch.** A tape's visited-set cardinality is at most the total space.
Heads are in the visited set; nonblank cells are in a prefix's visited set,
which is contained in that of the whole word. Apply the shared position bound. -/
private theorem runWith_take_inWindow (tm : NDTM k Bool S) (w : List Bool) {s : ℕ}
    (hs : tm.spaceUsedWith w (tm.initCfg x) ≤ s) (j : ℕ) :
    InWindow s (tm.runWith (w.take j) (tm.initCfg x)) := by
  intro i
  have card_bound : (tm.visitedWith w (tm.initCfg x) i).card ≤ s :=
    (Finset.single_le_sum (f := fun i => (tm.visitedWith w (tm.initCfg x) i).card)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hs
  have bounded (z : ℤ) (hz : z ∈ tm.visitedWith (w.take j) (tm.initCfg x) i) : |z| ≤ s := by
    have hz' := visitedWith_take_subset tm w (tm.initCfg x) j i hz
    have small := abs_lt_card_visitedWith tm w i hz'
    omega
  constructor
  · apply bounded
    apply Finset.mem_image.mpr
    exact ⟨(w.take j).length, Finset.mem_range.mpr (Nat.lt_succ_self _), by
      rw [List.take_length]⟩
  · intro z hz
    exact bounded z (mem_visitedWith_of_ne_none tm (w.take j) i z hz)

/-- Window validity depends only on the configuration-graph vertex. -/
private theorem inWindow_of_coreSum_eq {s : ℕ} {c d : Cfg k Bool S x}
    (h : coreSum c = coreSum d) (hd : InWindow s d) : InWindow s c := by
  have tapes : c.workTapes = d.workTapes := congrArg (fun v => v.1.2.2.1) h
  have heads : c.workTapePos = d.workTapePos := congrArg (fun v => v.1.2.2.2) h
  simpa only [InWindow, tapes, heads] using hd

/-- Deleting a segment between equal vertices preserves the final vertex and
makes every new prefix vertex an old prefix vertex. [AB09, §4.1.1]

**Proof sketch.** Before the cut, prefixes agree. After the cut, run the same
remaining choices from the two equal vertices and use `coreSum_runWith`.
The old index is the later cut index plus the length traversed after the cut. -/
private theorem splice_vertices (tm : NDTM k Bool S) (c : Cfg k Bool S x)
    (w : List Bool) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ w.length)
    (same : coreSum (tm.runWith (w.take a) c) = coreSum (tm.runWith (w.take b) c)) :
    coreSum (tm.runWith (w.take a ++ w.drop b) c) = coreSum (tm.runWith w c) ∧
    ∀ j ≤ (w.take a ++ w.drop b).length, ∃ l ≤ w.length,
      coreSum (tm.runWith ((w.take a ++ w.drop b).take j) c) =
        coreSum (tm.runWith (w.take l) c) := by
  have ha : a ≤ w.length := hab.trans hb
  constructor
  · simpa only [← runWith_append, List.take_append_drop] using coreSum_runWith tm (w.drop b) same
  · intro j hj
    by_cases before : j ≤ a
    · refine ⟨j, before.trans ha, ?_⟩
      rw [List.take_append_of_le_length (by simpa [List.length_take_of_le ha] using before),
        List.take_take, Nat.min_eq_left before]
    · refine ⟨b + (j - a), ?_, ?_⟩
      · simp only [List.length_append, List.length_take_of_le ha, List.length_drop] at hj
        omega
      · rw [List.take_append, List.take_take, Nat.min_eq_right (by omega : a ≤ j),
          List.length_take_of_le ha, List.take_add, runWith_append, runWith_append]
        exact coreSum_runWith tm ((w.drop b).take (j - a)) same

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

/-- Encode the three output summaries without adding a finiteness instance. -/
private def sumCode : OutSummary → Fin 3
  | .empty => 0
  | .accept => 1
  | .dead => 2

/-- Distinct summaries have distinct three-element codes. -/
private theorem sumCode_injective : Function.Injective sumCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [sumCode]

/-- Pairwise-distinct vertices of windowed configurations number at most the
configuration bound. [AB09, Claim 4.4(1)]

**Proof sketch.** Pair the received finite core code with the three-element
summary code. Windowedness supplies exactly the hypotheses of `coreCode_inj`.
The resulting injection has a finite codomain of the displayed cardinality. -/
private theorem count_windowed_vertices (N : FinNDTM Bool) (x : List Bool) (s t : ℕ)
    (cs : ℕ → Cfg N.k Bool N.State x)
    (window : ∀ j ≤ t, InWindow s (cs j))
    (distinct : Set.InjOn (fun j => NDTM.coreSum (cs j)) (Finset.range (t + 1))) :
    t + 1 ≤ N.configBound x.length s := by
  classical
  let code j := (MultiTapeTM.ConfigCount.coreCode s (cs j), sumCode (outSummary (cs j).output))
  have injective : Set.InjOn code (Finset.range (t + 1)) := by
    intro a ha b hb eqcode
    apply distinct ha hb
    apply Prod.ext
    · exact MultiTapeTM.ConfigCount.coreCode_inj s
        (window a (Nat.le_of_lt_succ (Finset.mem_range.mp ha)))
        (window b (Nat.le_of_lt_succ (Finset.mem_range.mp hb)))
        (congrArg Prod.fst eqcode)
    · exact sumCode_injective (congrArg Prod.snd eqcode)
  have card := Finset.card_le_card_of_injOn code (fun j _ => Finset.mem_univ (code j)) injective
  simp only [Finset.card_range, Finset.card_univ, Fintype.card_prod, Fintype.card_option,
    Fintype.card_fin, Fintype.card_pi, Finset.prod_const, Fintype.card_bool] at card
  rw [← pow_mul, Nat.mul_comm (2 * s + 1) N.k] at card
  convert card using 1
  simp only [configBound]
  ring

/-- No branch can accept before making a transition. [AB09, §4.1.1]

**Proof sketch.** The only zero-length choice word is empty, and the initial
configuration has a live control state. -/
theorem not_acceptsWithin_zero (N : FinNDTM Bool) (x : List Bool) :
    ¬ N.AcceptsWithin x 0 := by
  rintro ⟨w, hw, halted, _⟩
  have empty := List.length_eq_zero_iff.mp hw
  subst w
  simp at halted

/-- **Claim 4.4(1), acceptance form** (proved — phase P4.2): an
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
  classical
  by_cases short : T ≤ N.configBound x.length s
  · exact hacc.mono short
  obtain ⟨w, hw, halted, output⟩ := hacc
  -- Minimize among accepting words whose actual prefixes fit the coding window.
  let good (t : ℕ) : Prop := ∃ v : List Bool, v.length = t ∧
    (N.tm.runWith v (N.tm.initCfg x)).state = none ∧
    (N.tm.runWith v (N.tm.initCfg x)).output = [true] ∧
    ∀ j ≤ t, InWindow s (N.tm.runWith (v.take j) (N.tm.initCfg x))
  have exists_good : ∃ t, good t := ⟨T, w, hw, halted, output,
    fun j _ => NDTM.runWith_take_inWindow N.tm w (hs w hw) j⟩
  obtain ⟨v, hv, hvhalt, hvout, window⟩ := Nat.find_spec exists_good
  -- A repeated summary vertex produces a strictly shorter accepting word.
  have no_repeat (a b : ℕ) (ab : a < b) (bv : b ≤ v.length) :
      NDTM.coreSum (N.tm.runWith (v.take a) (N.tm.initCfg x)) ≠
        NDTM.coreSum (N.tm.runWith (v.take b) (N.tm.initCfg x)) := by
    intro same
    let u := v.take a ++ v.drop b
    obtain ⟨final, prefixes⟩ := NDTM.splice_vertices N.tm (N.tm.initCfg x) v ab.le bv same
    have shorter : u.length < Nat.find exists_good := by
      dsimp [u]
      rw [List.length_append, List.length_take_of_le (ab.le.trans bv), List.length_drop]
      omega
    have u_good : good u.length := by
      refine ⟨u, rfl, ?_, ?_, ?_⟩
      · exact (congrArg (fun vertex => vertex.1.1) final).trans hvhalt
      · apply (outSummary_eq_accept_iff _).mp
        exact (congrArg Prod.snd final).trans ((outSummary_eq_accept_iff _).mpr hvout)
      · intro j hj
        obtain ⟨l, hl, vertex⟩ := prefixes j hj
        exact NDTM.inWindow_of_coreSum_eq vertex (window l (hl.trans_eq hv))
    exact (Nat.not_le_of_lt shorter) (Nat.find_min' exists_good u_good)
  have distinct : Set.InjOn
      (fun j => NDTM.coreSum (N.tm.runWith (v.take j) (N.tm.initCfg x)))
      (Finset.range (Nat.find exists_good + 1)) := by
    intro a ha b hb same
    have a_bound := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have b_bound := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    by_contra ne
    rcases Nat.lt_or_gt_of_ne ne with ab | ba
    · exact no_repeat a b ab (by omega) same
    · exact no_repeat b a ba (by omega) same.symm
  have count := count_windowed_vertices N x s (Nat.find exists_good)
    (fun j => N.tm.runWith (v.take j) (N.tm.initCfg x)) window distinct
  exact (show N.AcceptsWithin x (Nat.find exists_good) from ⟨v, hv, hvhalt, hvout⟩).mono
    (by omega)

/-- **The packaged graph interface** (proved — phase P4.2): a
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
  obtain ⟨T, halt, space, iff_at_T⟩ := h x
  constructor
  · intro member
    exact acceptsWithin_of_spaceUsedWith_le N (iff_at_T.mp member) space
  · intro accepts
    apply iff_at_T.mpr
    by_cases budget : N.configBound x.length (s x.length) ≤ T
    · exact accepts.mono budget
    · obtain ⟨w, hw, _, output⟩ := accepts
      have prefix_length : (w.take T).length = T := List.length_take_of_le (by omega)
      have prefix_halt := halt (w.take T) prefix_length
      have frozen : N.tm.runWith w (N.tm.initCfg x) =
          N.tm.runWith (w.take T) (N.tm.initCfg x) := by
        conv_lhs => rw [← List.take_append_drop T w]
        rw [NDTM.runWith_append, NDTM.runWith_of_halt _ prefix_halt]
      exact ⟨w.take T, prefix_length, prefix_halt, by rw [← frozen]; exact output⟩

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
