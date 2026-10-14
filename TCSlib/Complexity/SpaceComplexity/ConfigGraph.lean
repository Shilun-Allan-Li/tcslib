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
import TCSlib.Complexity.TuringMachine.Build.RecordTable

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Configuration graphs of nondeterministic machines

[AB09, §4.1.1]: the configuration graph `G_{M,x}` of a machine on an input —
vertices the configurations, edges the one-step transitions (out-degree at most
two for a binary-choice NDTM) — together with the counting half of Claim 4.4(1)
for nondeterministic branches. This is phase P4.2 of `AroraBarakChapters3-4Plan.md`. The
exponential-time simulation ([AB09, Theorem 4.2, third inclusion]), `NL ⊆ P`, and the
coarseness of polynomial-time reductions below `P` ([AB09, Exercise 4.3]) were stated here;
their proof runs a breadth-first search over the configuration codec
(`TCSlib.Complexity.SpaceComplexity.Codec`), which imports this module, so they now live in
`TCSlib.Complexity.SpaceComplexity.ExpTime` with their statements unchanged. Savitch's
theorem, the other consumer of this layer, is `TCSlib.Complexity.SpaceComplexity.Savitch`.

**Status: graph lemmas proved (phase P4.2, batch S1a).** The four graph contracts are proved;
`Complexity.NSPACE_subset_exp_dtime`, `Complexity.NL_subset_P` and
`Complexity.polyTimeReducible_of_mem_NL` are proved in
`TCSlib.Complexity.SpaceComplexity.ExpTime` (2026-10-14). The private `s1b_*` helpers below
belong to the superseded record-table route of the S1b partial fill and have no consumer.
`spaceConstructible_logSpace` is proved (B3a).

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

## Main results

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

/-- The graph window and the public record window agree. This is the single
bridge allowed by S1b ground rule 10; S1a's declarations remain unchanged.

**Proof sketch.** Separate the head bounds and contrapose the cell bounds. -/
private theorem inWindow_iff_cfgInWindow (s : ℕ) (c : Cfg k Bool S x) :
    InWindow s c ↔ c.InWindow s := by
  constructor
  · intro h
    refine ⟨fun i => (h i).1, ?_⟩
    intro i z hz
    by_contra nonblank
    exact (not_le_of_gt hz) ((h i).2 z nonblank)
  · rintro ⟨heads, cells⟩ i
    refine ⟨heads i, ?_⟩
    intro z nonblank
    by_contra outside
    exact nonblank (cells i z (lt_of_not_ge outside))

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

/-- The canonical rich record of a graph vertex, using S1a's summary code.
It records precisely the core and output summary, not the output history. -/
private def s1b_record (s : ℕ) (c : Cfg k Bool S x) : List (List (RecSym S (Fin 3))) :=
  cfgRecord s c (sumCode (outSummary c.output))

/-- Canonical records identify exactly S1a's vertices on the coding window.
This is the decoding part of the note-6 bridge, a Savitch promotion candidate.

**Proof sketch.** The received `cfgRecord_inj` recovers all four core fields
and the tag. S1a's injective `sumCode` recovers the output summary. -/
private theorem s1b_record_eq_iff {s : ℕ} {c d : Cfg k Bool S x}
    (hc : c.InWindow s) (hd : d.InWindow s) :
    s1b_record s c = s1b_record s d ↔ NDTM.coreSum c = NDTM.coreSum d := by
  rw [s1b_record, s1b_record, cfgRecord_inj s hc hd]
  simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core, Prod.mk.injEq,
    sumCode_injective.eq_iff]

/-- The quotient edge implemented by the two record-step calls. Requiring
the successor window is the semantic rejection of an outside-window step;
the received `exists_recordStepTM` supplies the machine's `no` branch. -/
private def s1b_recordEdge (tm : NDTM k Bool S) (s : ℕ)
    (fs gs : List (List (RecSym S (Fin 3)))) : Prop :=
  ∃ (c : Cfg k Bool S x) (b : Bool), c.InWindow s ∧ (tm.stepWith b c).InWindow s ∧
    fs = s1b_record s c ∧ gs = s1b_record s (tm.stepWith b c)

/-- Every path of canonical records lifts to a choice-word run from the
supplied actual configuration, in particular the true initial configuration.
The reflexive case uses the empty word. This is part of the note-6 promotion
candidate; it does not assert a table-machine invariant.

**Proof sketch.** At each quotient edge decode equality with its source,
apply S1a's `coreSum_stepWith`, and transfer window validity from the edge's
representative. Append that edge's bit to the actual run. -/
private theorem s1b_recordPath_lift (tm : NDTM k Bool S) {s : ℕ}
    {c : Cfg k Bool S x} (hc : c.InWindow s) {fs : List (List (RecSym S (Fin 3)))}
    (path : Relation.ReflTransGen (s1b_recordEdge (x := x) tm s) (s1b_record s c) fs) :
    ∃ w : List Bool, (tm.runWith w c).InWindow s ∧ s1b_record s (tm.runWith w c) = fs := by
  induction path with
  | refl => exact ⟨[], hc, rfl⟩
  | @tail fs gs _ edge ih =>
    obtain ⟨w, hw, hrecord⟩ := ih
    obtain ⟨d, b, hd, hnext, hfs, hgs⟩ := edge
    have same := (s1b_record_eq_iff hw hd).mp (hrecord.trans hfs)
    have next := NDTM.coreSum_stepWith tm b same
    have window : (tm.stepWith b (tm.runWith w c)).InWindow s :=
      (inWindow_iff_cfgInWindow _ _).mp
        (NDTM.inWindow_of_coreSum_eq next ((inWindow_iff_cfgInWindow _ _).mpr hnext))
    refine ⟨w ++ [b], ?_, ?_⟩
    · simpa only [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil] using window
    · simpa only [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil] using
        ((s1b_record_eq_iff window hnext).mpr next).trans hgs.symm

/-- A run whose prefixes stay in the window gives a path of canonical
records, including the zero-step path. This is the reverse direction of the
note-6 bridge, independent of a table representation.

**Proof sketch.** Each first bit gives one quotient edge; the remaining
prefixes are exactly the positive-length prefixes of the original word. -/
private theorem s1b_recordPath_of_run (tm : NDTM k Bool S) (s : ℕ) (w : List Bool)
    (c : Cfg k Bool S x) (hwindow : ∀ j, (tm.runWith (w.take j) c).InWindow s) :
    Relation.ReflTransGen (s1b_recordEdge (x := x) tm s)
      (s1b_record s c) (s1b_record s (tm.runWith w c)) := by
  induction w generalizing c with
  | nil => exact Relation.ReflTransGen.refl
  | cons b w ih =>
    have hc : c.InWindow s := by simpa using hwindow 0
    have hb : (tm.stepWith b c).InWindow s := by simpa using hwindow 1
    apply Relation.ReflTransGen.head ⟨c, b, hc, hb, rfl, rfl⟩
    apply ih
    intro j
    simpa only [List.take_succ_cons, NDTM.runWith_cons] using hwindow (j + 1)

/-- Representatives of the three summary codes, used only to compute tag
updates. The encoding itself is the received `sumCode`. -/
private def s1b_summaryWord (τ : Fin 3) : List Bool :=
  if τ = sumCode .empty then [] else if τ = sumCode .accept then [true] else [false]

/-- Each chosen representative has the requested summary code.

**Proof sketch.** Check the three elements of `Fin 3`; the existing encoding
computes on the empty, accepting and dead representative words. -/
private theorem s1b_summaryWord_code (τ : Fin 3) :
    sumCode (outSummary (s1b_summaryWord τ)) = τ := by
  fin_cases τ <;> rfl

/-- The record-step tag update is summary append on a representative word. -/
private def s1b_tagUpdate (τ : Fin 3) (b : Option Bool) : Fin 3 :=
  sumCode (outSummary (s1b_summaryWord τ ++ b.toList))

/-- An absent emission preserves the tag, as required by `recordStepTM`.

**Proof sketch.** Appending no symbol preserves the representative word. -/
private theorem s1b_tagUpdate_none (τ : Fin 3) : s1b_tagUpdate τ none = τ := by
  simpa [s1b_tagUpdate] using s1b_summaryWord_code τ

/-- The finite tag update agrees with every actual output history.

**Proof sketch.** The representative and actual word have equal summaries
by injectivity of S1a's code. Apply its append-congruence theorem. -/
private theorem s1b_tagUpdate_output (u : List Bool) (b : Option Bool) :
    s1b_tagUpdate (sumCode (outSummary u)) b = sumCode (outSummary (u ++ b.toList)) := by
  exact congrArg sumCode (outSummary_append_congr
    (sumCode_injective (s1b_summaryWord_code (sumCode (outSummary u)))) b.toList)

/-- The verdict is a predicate on every decoded record, with no distinguished
accepting vertex. Equality of records preserves it even when output histories
differ. [AB09, §4.1.1]

**Proof sketch.** A record's tag accepts precisely when the summary is
`accept`, by S1a's injective code; its summary accepts precisely `[true]`. -/
private theorem s1b_record_accepts (c : Cfg k Bool S x) :
    (c.state = none ∧ sumCode (outSummary c.output) = sumCode .accept) ↔
      c.Halted ∧ c.output = [true] := by
  rw [sumCode_injective.eq_iff, outSummary_eq_accept_iff]

end FinNDTM

end Turing

namespace Complexity

open Turing

/-- The configuration-count formula is exponential in any bound dominating
`logSpace`, with no monotonicity assumption. [AB09, Claim 4.4(1)]
This formula-level helper is a promotion candidate for Savitch.

**Proof sketch.** P4.2 Question 5 bounds the input factor by `2^(u+1)`,
the cell alphabet by `2^2`, and the head range by `2^(a*u+1)`.
Multiplication adds the exponents; the displayed coefficient absorbs their
constant terms and the finite state factor. -/
private theorem s1b_count_le_exp (q k a n u : ℕ) (hu : logSpace n ≤ u) :
    (q + 1) * (n + 2) * 3 ^ (k * (2 * (a * u) + 1)) * (2 * (a * u) + 1) ^ k ≤
      2 ^ ((q + 2 + k * (5 * a + 3)) * (u + 1)) := by
  have input : n + 2 ≤ 2 ^ (u + 1) := by
    have hn : n + 1 ≤ 2 ^ u :=
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).trans_le
        (Nat.pow_le_pow_right (by decide) hu)
    have hp : 0 < 2 ^ u := Nat.two_pow_pos u
    rw [pow_succ]
    omega
  have head : 2 * (a * u) + 1 ≤ 2 ^ (a * u + 1) := by
    have hp := Nat.lt_two_pow_self (n := a * u)
    rw [pow_succ]
    omega
  calc
    _ ≤ 2 ^ (q + 1) * 2 ^ (u + 1) *
        (2 ^ 2) ^ (k * (2 * (a * u) + 1)) * (2 ^ (a * u + 1)) ^ k :=
      Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_two_pow_self (n := q + 1))) input)
          (Nat.pow_le_pow_left (by decide : 3 ≤ 2 ^ 2) _))
        (Nat.pow_le_pow_left head k)
    _ = 2 ^ ((q + 1) + (u + 1) + 2 * (k * (2 * (a * u) + 1)) + (a * u + 1) * k) := by
      simp only [← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)

/-- The formula-level bound instantiated for the deterministic constructor.

**Proof sketch.** Unfold only the received count definition and apply the
single generalized counting argument. -/
private theorem s1b_constructor_count (M : FinTM Bool) (a n u : ℕ)
    (hu : logSpace n ≤ u) :
    M.configBound n (a * u) ≤
      2 ^ ((Fintype.card M.State + 2 + M.k * (5 * a + 3)) * (u + 1)) :=
  s1b_count_le_exp (Fintype.card M.State) M.k a n u hu

/-- The same formula-level bound, including the three output summaries, for
the nondeterministic graph. [AB09, Claim 4.4(1)]

**Proof sketch.** The received vertex count is three times the core count.
Bound three by four and absorb the two extra exponent units into the fixed
coefficient. -/
private theorem s1b_vertex_count (N : FinNDTM Bool) (a n u : ℕ)
    (hu : logSpace n ≤ u) :
    N.configBound n (a * u) ≤
      2 ^ ((Fintype.card N.State + 4 + N.k * (5 * a + 3)) * (u + 1)) := by
  unfold FinNDTM.configBound
  calc
    _ ≤ 2 ^ 2 * 2 ^ ((Fintype.card N.State + 2 + N.k * (5 * a + 3)) * (u + 1)) :=
      Nat.mul_le_mul (by decide) (s1b_count_le_exp _ _ _ _ _ hu)
    _ = 2 ^ (2 + (Fintype.card N.State + 2 + N.k * (5 * a + 3)) * (u + 1)) :=
      (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)

/-- Normalizing the space constant does not change the deciding machine or
any branch's halting budget. No monotonicity of the space function is needed.

**Proof sketch.** Choose the original constant itself as the exponent, since
`c ≤ 2^c`. Enlarge only the space inequality in each received witness. The
constructibility lower bound makes the binary radius word canonical. -/
private theorem s1b_normalize_radius {S : ℕ → ℕ} (hdom : ∀ n, logSpace n ≤ S n)
    {L : Language Bool} {N : FinNDTM Bool} {c : ℕ}
    (hN : N.DecidesInSpace L fun n => c * S n) :
    ∃ j : ℕ, c ≤ 2 ^ j ∧
      N.DecidesInSpace L (fun n => 2 ^ j * S n) ∧
      ∀ n, (2 ^ j * S n).bits = List.replicate j false ++ (S n).bits := by
  have hc : c ≤ 2 ^ c := Nat.le_of_lt (Nat.lt_two_pow_self (n := c))
  refine ⟨c, hc, ?_, ?_⟩
  · intro x
    obtain ⟨T, hhalt, hspace, hacc⟩ := hN x
    exact ⟨T, hhalt, fun w hw => (hspace w hw).trans (Nat.mul_le_mul_right _ hc), hacc⟩
  · intro n
    apply bits_two_pow_mul
    have := hdom n
    unfold logSpace at this
    omega

/-- The received deterministic count supplies the constructor's time bound.
This isolates the noncircular time ledger of the radius phase.

**Proof sketch.** Each space-constructor witness already halts. Apply
`ComputesInTime.of_spaceUsed_le` to its finite run, then the deterministic
instance of the generalized count. -/
private theorem s1b_constructor_time {S : ℕ → ℕ} (hdom : ∀ n, logSpace n ≤ S n)
    {M : FinTM Bool} {a : ℕ}
    (hM : M.ComputesInSpace (fun x => (S x.length).bits) fun n => a * S n) :
    ∀ x, M.ComputesInTime x (S x.length).bits (M.configBound x.length (a * S x.length)) ∧
      M.configBound x.length (a * S x.length) ≤
        2 ^ ((Fintype.card M.State + 2 + M.k * (5 * a + 3)) * (S x.length + 1)) := by
  intro x
  obtain ⟨t, ht, hs⟩ := hM x
  exact ⟨ht.of_spaceUsed_le hs, s1b_constructor_count M a x.length (S x.length) (hdom _)⟩

end Complexity
