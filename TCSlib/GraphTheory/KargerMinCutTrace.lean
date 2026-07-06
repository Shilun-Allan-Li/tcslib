/-
Copyright (c) 2026 Joon Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joon Kim
-/

import TCSlib.GraphTheory.KargerMinCut

open scoped BigOperators
open Finset Nat

set_option linter.unnecessarySimpa false
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Karger's MinCut: Algorithmic Trace Proof

This file contains the accurate algorithmic proof layer for Karger's fixed
min-cut survival argument.

The imported file proves the local graph facts:

* non-crossing contraction preserves cut size,
* non-crossing contraction preserves the min-cut property,
* a min-cut is bounded by every degree,
* handshaking gives the edge-count lower bound.

Here we package those facts into adaptive contraction traces and a recursive
finite probability model.

## Main results

* `fixed_mincut_survival_probability_lower_bound`: a fixed positive min-cut
  survives the recursive adaptive edge-choice process with probability at least
  `2 / (n * (n - 1))`.
* `adaptive_karger_trace_outputs_two_vertices`: every adaptive graph trace of
  `n - 2` contractions ends with two vertices.
* `adaptive_karger_trace_main`: the previous two statements bundled together.

Many smaller lemmas in this file are Lean plumbing: they turn multiset edge
occurrences into valid contractions, move cut invariants along traces, and make
finite sums line up with probability ratios.

## References

- Karger, D.R. (1993): Global min-cuts in RNC, and other ramifications of a simple
  min-cut algorithm.
-/

namespace KargerTrace

/-! ## States and Surviving Contractions -/

/-- A state consists of the current multigraph and the current distinguished cut. -/
structure State (α : Type*) [DecidableEq α] where
  G : Multigraph α
  C : MulCut G

/-- Contract a non-crossing edge and carry the cut along the contraction. -/
noncomputable def contractState {α : Type*} [DecidableEq α]
    (s : State α) (e : Sym2 α) (he : e ∈ s.G.edges)
    (hsurvive : e ∉ s.C.crossingEdges) : State α :=
  { G := s.G.contract e he
    C := s.C.contractedCut e he hsurvive }

/-- A single surviving step: the chosen edge does not cross the distinguished cut.
    Human intuition: there exists a non-crossing edge such that s transforms into t
    by contracting it. -/
def SurvivingStep {α : Type*} [DecidableEq α] (s t : State α) : Prop :=
  ∃ (e : Sym2 α) (he : e ∈ s.G.edges) (hsurvive : e ∉ s.C.crossingEdges),
    t = contractState s e he hsurvive

/-- A trace of `n` surviving contractions. -/
inductive SurvivingRun {α : Type*} [DecidableEq α] :
    ℕ → State α → State α → Prop
  | nil (s : State α) : SurvivingRun 0 s s
  | cons {n : ℕ} {s t u : State α}
      (h : SurvivingRun n s t) (hstep : SurvivingStep t u) :
      SurvivingRun (n + 1) s u

/-! ## Trace Invariants -/

/- First, we prove invariants on a single step. -/

/-- There exists at least one edge. -/
lemma edgeCount_pos_of_mem {α : Type*} [DecidableEq α]
    {G : Multigraph α} {e : Sym2 α} (he : e ∈ G.edges) :
    0 < G.edgeCount := by
  rw [Multigraph.edgeCount]
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨e, he⟩

/-- 1) A surviving step doesn't change the cut size of C. -/
lemma survivingStep_cut_size_eq {α : Type*} [DecidableEq α]
    {s t : State α} (hstep : SurvivingStep s t) :
    t.C.size = s.C.size := by
  rcases hstep with ⟨e, he, hsurvive, rfl⟩
  exact cut_size_preserved s.C e he hsurvive

/-- 2) A surviving step preserves the min-cut property of C. -/
lemma survivingStep_mincut {α : Type*} [DecidableEq α]
    {s t : State α} (hstep : SurvivingStep s t)
    (hmin : IsMulMinCut s.C) :
    IsMulMinCut t.C := by
  rcases hstep with ⟨e, he, hsurvive, rfl⟩
  exact mincut_preserved_of_non_crossing s.C hmin e he hsurvive

/-- 3) A surviving step removes exactly one vertex. -/
lemma survivingStep_vertexCount_eq {α : Type*} [DecidableEq α]
    {s t : State α} (hstep : SurvivingStep s t) :
    t.G.vertexCount = s.G.vertexCount - 1 := by
  rcases hstep with ⟨e, he, hsurvive, rfl⟩
  have hne : ¬ e.IsDiag := s.G.loopless e he
  simpa [contractState] using contract_vertex_count s.G e he hne

/-- The existence of a contracted state from s implies nonzero edge count of s. -/
lemma survivingStep_edgeCount_pos {α : Type*} [DecidableEq α]
    {s t : State α} (hstep : SurvivingStep s t) :
    0 < s.G.edgeCount := by
  rcases hstep with ⟨e, he, _hsurvive, _⟩
  exact edgeCount_pos_of_mem he

/- Now we show that the invariant is carried throughout the entire run.
    There is a one-to-one correspondence with the step invariants.-/

/-- 1) A surviving run doesn't change the cut size of C. -/
lemma survivingRun_cut_size_eq {α : Type*} [DecidableEq α]
    {n : ℕ} {s t : State α} (h : SurvivingRun n s t) :
    t.C.size = s.C.size := by
  induction h with
  | nil s =>
      rfl
  | cons hrun hstep ih =>
      exact (survivingStep_cut_size_eq hstep).trans ih

/-- 2) A surviving run preserves the min-cut property of C. -/
lemma survivingRun_mincut {α : Type*} [DecidableEq α]
    {n : ℕ} {s t : State α} (h : SurvivingRun n s t)
    (hmin : IsMulMinCut s.C) :
    IsMulMinCut t.C := by
  induction h with
  | nil s =>
      exact hmin
  | cons hrun hstep ih =>
      exact survivingStep_mincut hstep (ih hmin)

/-- 3) An n-step surviving run removes exactly n vertices. -/
lemma survivingRun_vertexCount_eq {α : Type*} [DecidableEq α]
    {n : ℕ} {s t : State α} (h : SurvivingRun n s t) :
    t.G.vertexCount = s.G.vertexCount - n := by
  induction h with
  | nil s =>
      simp
  | cons hrun hstep ih =>
      have hstep_v := survivingStep_vertexCount_eq hstep
      rw [hstep_v, ih]
      omega

/-- The actual trace-level edge-count invariant.

This is the first main bridge missing from the karger_algorithmic file: the lower bound is
now stated for the graph reached after `n` surviving contractions, not only for
the original graph.
-/
lemma survivingRun_edge_count_invariant {α : Type*} [DecidableEq α]
    {n : ℕ} {s t : State α} (h : SurvivingRun n s t)
    (hmin : IsMulMinCut s.C) :
    s.C.size * t.G.vertexCount ≤ 2 * t.G.edgeCount := by
  have hmin_t : IsMulMinCut t.C := survivingRun_mincut h hmin
  have hbase : t.C.size * t.G.vertexCount ≤ 2 * t.G.edgeCount := by
    refine edge_count_lower_bound t.C.size ?_
    intro v hv
    exact mincut_le_degree t.C hmin_t hv
  have hsize : t.C.size = s.C.size := survivingRun_cut_size_eq h
  simpa [hsize] using hbase

/-- The indexed version of the trace invariant, using the vertex count after
`n` contractions. -/
lemma survivingRun_edge_count_invariant_indexed {α : Type*} [DecidableEq α]
    {n : ℕ} {s t : State α} (h : SurvivingRun n s t)
    (hmin : IsMulMinCut s.C) :
    s.C.size * (s.G.vertexCount - n) ≤ 2 * t.G.edgeCount := by
  have hvc : t.G.vertexCount = s.G.vertexCount - n :=
    survivingRun_vertexCount_eq h
  simpa [← hvc] using survivingRun_edge_count_invariant h hmin

/-! ## One-Step Survival Bound -/

/-- Algebraic one-step survival lower bound.

If a graph with `n` vertices and `m` edges has a min-cut of size `c`, and
`c * n ≤ 2m`, then the probability of not choosing a cut edge is at least
`(n - 2) / n`.
-/
lemma survivalProb_ge_factor {c n m : ℕ}
    (hn : 2 ≤ n) (hm : 0 < m) (hbound : c * n ≤ 2 * m) :
    ((n - 2 : ℕ) : ℝ) / n ≤ survivalProb c m := by
  have hn_pos_nat : 0 < n := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos_nat
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  have hbound_real : (c : ℝ) * (n : ℝ) ≤ (2 : ℝ) * (m : ℝ) := by
    exact_mod_cast hbound
  have hcut_ratio : (c : ℝ) / (m : ℝ) ≤ (2 : ℝ) / (n : ℝ) := by
    rw [div_le_div_iff₀ hm_pos hn_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbound_real
  have hfactor : ((n - 2 : ℕ) : ℝ) / (n : ℝ) = 1 - (2 : ℝ) / (n : ℝ) := by
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    rw [Nat.cast_sub hn]
    field_simp [hn_ne]
    ring
  rw [hfactor, survivalProb]
  linarith

/-- One-step version specialized to a surviving state.

This packages the degree/handshaking invariant into the exact lower bound used
for each conditional survival factor in Karger's proof.
-/
lemma survivingStep_survivalProb_ge_factor {α : Type*} [DecidableEq α]
    {s t : State α} (hstep : SurvivingStep s t)
    (hmin : IsMulMinCut s.C) (hn : 2 ≤ s.G.vertexCount) :
    ((s.G.vertexCount - 2 : ℕ) : ℝ) / s.G.vertexCount ≤
      survivalProb s.C.size s.G.edgeCount := by
  have hm : 0 < s.G.edgeCount := survivingStep_edgeCount_pos hstep
  have hbound : s.C.size * s.G.vertexCount ≤ 2 * s.G.edgeCount := by
    refine edge_count_lower_bound s.C.size ?_
    intro v hv
    exact mincut_le_degree s.C hmin hv
  exact survivalProb_ge_factor hn hm hbound

/-- Trace-indexed one-step lower bound at the state reached after `i`
surviving contractions. -/
lemma survivingRun_survivalProb_ge_factor {α : Type*} [DecidableEq α]
    {i : ℕ} {s t u : State α}
    (hrun : SurvivingRun i s t) (hstep : SurvivingStep t u)
    (hmin : IsMulMinCut s.C) (hn : 2 ≤ t.G.vertexCount) :
    ((t.G.vertexCount - 2 : ℕ) : ℝ) / t.G.vertexCount ≤
      survivalProb s.C.size t.G.edgeCount := by
  have hmin_t : IsMulMinCut t.C := survivingRun_mincut hrun hmin
  have hm : 0 < t.G.edgeCount := survivingStep_edgeCount_pos hstep
  have hbound_t : t.C.size * t.G.vertexCount ≤ 2 * t.G.edgeCount := by
    refine edge_count_lower_bound t.C.size ?_
    intro v hv
    exact mincut_le_degree t.C hmin_t hv
  have hsize : t.C.size = s.C.size := survivingRun_cut_size_eq hrun
  have hbound_s : s.C.size * t.G.vertexCount ≤ 2 * t.G.edgeCount := by
    simpa [hsize] using hbound_t
  exact survivalProb_ge_factor hn hm hbound_s

/-! ## Concrete Edge-Choice Probability -/

/-- The actual edge choices that preserve the distinguished cut at state `s`. -/
noncomputable def nonCrossingEdges {α : Type*} [DecidableEq α]
    (s : State α) : Multiset (Sym2 α) :=
  s.G.edges.filter fun e => ¬ Crosses s.C.S e

/-- Number of uniformly available edge choices that preserve the cut. -/
noncomputable def nonCrossingChoiceCount {α : Type*} [DecidableEq α]
    (s : State α) : ℕ :=
  (nonCrossingEdges s).card

/-- Concrete one-step survival probability under a uniform edge choice. -/
noncomputable def uniformSurvivalProb {α : Type*} [DecidableEq α]
    (s : State α) : ℝ :=
  (nonCrossingChoiceCount s : ℝ) / s.G.edgeCount

lemma nonCrossingChoiceCount_eq_edgeCount_sub_cutSize
    {α : Type*} [DecidableEq α] (s : State α) :
    nonCrossingChoiceCount s = s.G.edgeCount - s.C.size := by
  have htotal :=
    Multiset.card_eq_countP_add_countP (p := Crosses s.C.S) s.G.edges
  rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter] at htotal
  have hcross :
      (s.G.edges.filter (Crosses s.C.S)).card = s.C.size := by
    rw [← crossingEdges_eq_filter_crosses s.C]
    rfl
  have hnoncross :
      (s.G.edges.filter (fun e => ¬ Crosses s.C.S e)).card =
        nonCrossingChoiceCount s := by
    rfl
  rw [hcross, hnoncross] at htotal
  unfold Multigraph.edgeCount
  omega

lemma cut_size_le_edgeCount {α : Type*} [DecidableEq α] (s : State α) :
    s.C.size ≤ s.G.edgeCount := by
  rw [MulCut.size, Multigraph.edgeCount, MulCut.crossingEdges]
  exact Multiset.card_le_card (Multiset.filter_le _ s.G.edges)

/-- Algorithmically choosing an edge uniformly gives the desired survival probability. -/
lemma uniformSurvivalProb_eq_survivalProb
    {α : Type*} [DecidableEq α] (s : State α)
    (hm : 0 < s.G.edgeCount) :
    uniformSurvivalProb s = survivalProb s.C.size s.G.edgeCount := by
  have hle : s.C.size ≤ s.G.edgeCount := cut_size_le_edgeCount s
  have hm_ne : (s.G.edgeCount : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  rw [uniformSurvivalProb, nonCrossingChoiceCount_eq_edgeCount_sub_cutSize, survivalProb]
  rw [Nat.cast_sub hle]
  field_simp [hm_ne]

/-- Finite sample space of edge occurrences for a uniform edge choice.

The second coordinate distinguishes parallel copies of the same edge.
-/
noncomputable def edgeChoiceSpace {α : Type*} [DecidableEq α]
    (s : State α) : Finset (Sym2 α × ℕ) :=
  s.G.edges.toEnumFinset

def edgeChoiceSurvives {α : Type*} [DecidableEq α]
    (s : State α) (choice : Sym2 α × ℕ) : Prop :=
  ¬ Crosses s.C.S choice.1

noncomputable instance edgeChoiceSurvivesDecidable
    {α : Type*} [DecidableEq α] (s : State α) :
    DecidablePred (edgeChoiceSurvives s) := by
  classical
  intro choice
  dsimp [edgeChoiceSurvives]
  infer_instance

lemma edgeChoiceSpace_card {α : Type*} [DecidableEq α] (s : State α) :
    (edgeChoiceSpace s).card = s.G.edgeCount := by
  simp [edgeChoiceSpace, Multigraph.edgeCount, Multiset.card_toEnumFinset]

lemma toEnumFinset_filter_fst_card_eq_filter_card
    {α : Type*} [DecidableEq α] (m : Multiset α)
    (p : α → Prop) [DecidablePred p] :
    (m.toEnumFinset.filter fun x => p x.1).card = (m.filter p).card := by
  have hmap :
      Multiset.map Prod.fst m.toEnumFinset.1 = m := by
    simpa using Multiset.map_toEnumFinset_fst m
  have hcount_map :
      Multiset.countP p (Multiset.map Prod.fst m.toEnumFinset.1) =
        (m.toEnumFinset.1.filter fun x => p x.1).card := by
    simpa using Multiset.countP_map Prod.fst m.toEnumFinset.1 p
  have hcount_m :
      Multiset.countP p m = (m.filter p).card := by
    exact Multiset.countP_eq_card_filter (p := p) m
  have hfinset :
      (m.toEnumFinset.filter fun x => p x.1).card =
        (m.toEnumFinset.1.filter fun x => p x.1).card := by
    rfl
  rw [hfinset, ← hcount_map, hmap, hcount_m]

lemma edgeChoiceSurvivalCount_eq_nonCrossingChoiceCount
    {α : Type*} [DecidableEq α] (s : State α) :
    ((edgeChoiceSpace s).filter (edgeChoiceSurvives s)).card =
      nonCrossingChoiceCount s := by
  unfold edgeChoiceSpace edgeChoiceSurvives nonCrossingChoiceCount nonCrossingEdges
  exact toEnumFinset_filter_fst_card_eq_filter_card s.G.edges (fun e => ¬ Crosses s.C.S e)

/-- Concrete one-step survival probability as a ratio of finite sample-space
counts. -/
noncomputable def edgeChoiceSurvivalRatio {α : Type*} [DecidableEq α]
    (s : State α) : ℝ :=
  (((edgeChoiceSpace s).filter (edgeChoiceSurvives s)).card : ℝ) /
    (edgeChoiceSpace s).card

lemma edgeChoiceSurvivalRatio_eq_uniformSurvivalProb
    {α : Type*} [DecidableEq α] (s : State α) :
    edgeChoiceSurvivalRatio s = uniformSurvivalProb s := by
  rw [edgeChoiceSurvivalRatio, uniformSurvivalProb,
    edgeChoiceSurvivalCount_eq_nonCrossingChoiceCount, edgeChoiceSpace_card]

/-! ## Recursive Adaptive Survival Probability -/

/-- An edge occurrence in `edgeChoiceSpace s` carries an actual edge of `s.G`.

The occurrence index only distinguishes parallel copies; the first projection is
the edge contracted by the algorithm.
-/
lemma edgeChoice_mem_edges {α : Type*} [DecidableEq α]
    (s : State α) (choice : {x // x ∈ edgeChoiceSpace s}) :
    choice.1.1 ∈ s.G.edges := by
  exact Multiset.mem_of_mem_toEnumFinset (by
    simpa [edgeChoiceSpace] using choice.2)

lemma not_mem_crossingEdges_of_edgeChoiceSurvives
    {α : Type*} [DecidableEq α] (s : State α)
    (choice : {x // x ∈ edgeChoiceSpace s})
    (hsurvive : edgeChoiceSurvives s choice.1) :
    choice.1.1 ∉ s.C.crossingEdges := by
  intro hcross
  have hcross' : choice.1.1 ∈ s.G.edges.filter (Crosses s.C.S) := by
    simpa [crossingEdges_eq_filter_crosses s.C] using hcross
  exact hsurvive (Multiset.mem_filter.mp hcross').2

/-- The successor state obtained from a sampled edge occurrence, when that
occurrence does not cross the distinguished cut. -/
noncomputable def stateAfterSurvivingChoice
    {α : Type*} [DecidableEq α] (s : State α)
    (choice : {x // x ∈ edgeChoiceSpace s})
    (hsurvive : edgeChoiceSurvives s choice.1) : State α :=
  contractState s choice.1.1 (edgeChoice_mem_edges s choice)
    (not_mem_crossingEdges_of_edgeChoiceSurvives s choice hsurvive)

/-- Choosing a non-crossing edge yields a valid surviving state after contraction. -/
lemma stateAfterSurvivingChoice_step
    {α : Type*} [DecidableEq α] (s : State α)
    (choice : {x // x ∈ edgeChoiceSpace s})
    (hsurvive : edgeChoiceSurvives s choice.1) :
    SurvivingStep s (stateAfterSurvivingChoice s choice hsurvive) := by
  exact ⟨choice.1.1, edgeChoice_mem_edges s choice,
    not_mem_crossingEdges_of_edgeChoiceSurvives s choice hsurvive, rfl⟩

/-- Recursive finite probability that the distinguished cut survives the next
`steps` random edge-occurrence choices.

At each nonzero step we average over all edge occurrences. Branches that pick a
crossing edge contribute `0`; branches that pick a non-crossing edge recurse on
the contracted state.

Human intution: This is internalizing the conditional probability of the algorithm;
we only care about the traces that gives us the desired min-cut at the end.
-/
noncomputable def survivalEventProb {α : Type*} [DecidableEq α] :
    ℕ → State α → ℝ
  | 0, _ => 1
  | steps + 1, s =>
      ((edgeChoiceSpace s).attach.sum fun choice =>
        if hsurvive : edgeChoiceSurvives s choice.1 then
          survivalEventProb steps (stateAfterSurvivingChoice s choice hsurvive)
        else 0) / (edgeChoiceSpace s).card

/-- Base case: If we have no more contractions to apply, we have survived. -/
@[simp] lemma survivalEventProb_zero
    {α : Type*} [DecidableEq α] (s : State α) :
    survivalEventProb 0 s = 1 := rfl

/-- Induction: If we have to contract, look at all possible ways to contract,
    and find the average probability of succeeding in each of them. -/
lemma survivalEventProb_succ
    {α : Type*} [DecidableEq α] (steps : ℕ) (s : State α) :
    survivalEventProb (steps + 1) s =
      ((edgeChoiceSpace s).attach.sum fun choice =>
        if hsurvive : edgeChoiceSurvives s choice.1 then
          survivalEventProb steps (stateAfterSurvivingChoice s choice hsurvive)
        else 0) / (edgeChoiceSpace s).card := rfl

lemma edgeChoice_attach_filter_card
    {α : Type*} [DecidableEq α] (s : State α) :
    ((edgeChoiceSpace s).attach.filter fun choice =>
      edgeChoiceSurvives s choice.1).card =
        ((edgeChoiceSpace s).filter (edgeChoiceSurvives s)).card := by
  classical
  simpa using congrArg Finset.card
    (Finset.filter_attach (p := edgeChoiceSurvives s) (s := edgeChoiceSpace s))

lemma card_mul_le_sum_ite_of_lower_bound
    {β : Type*} [DecidableEq β] (S : Finset β)
    (p : β → Prop) [DecidablePred p] (f : β → ℝ) {B : ℝ}
    (hf : ∀ x ∈ S, p x → B ≤ f x) :
    ((S.filter p).card : ℝ) * B ≤
      ∑ x ∈ S, if p x then f x else 0 := by
  calc
    ((S.filter p).card : ℝ) * B
        = ∑ _x ∈ S.filter p, B := by
            simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ S.filter p, f x := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact hf x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
    _ = ∑ x ∈ S, if p x then f x else 0 := by
          rw [Finset.sum_filter]

/-- If every surviving branch has recursive survival probability at least `B`,
then the one-step averaged survival probability is at least the concrete
survival ratio times `B`.

Human intuition: Pr[surviving from t-th step onwards] ≥
                  Pr[survives t-th step]*
                  min(Pr[surviving from (t+1)-th step onwards | survived t-th step]) -/
lemma survivalEventProb_step_lower_bound
    {α : Type*} [DecidableEq α] (s : State α) (steps : ℕ)
    {B : ℝ} (hm : 0 < (edgeChoiceSpace s).card)
    (hind : ∀ (choice : {x // x ∈ edgeChoiceSpace s})
      (hsurvive : edgeChoiceSurvives s choice.1),
        B ≤ survivalEventProb steps
          (stateAfterSurvivingChoice s choice hsurvive)) :
    edgeChoiceSurvivalRatio s * B ≤ survivalEventProb (steps + 1) s := by
  classical
  let S : Finset {x // x ∈ edgeChoiceSpace s} := (edgeChoiceSpace s).attach
  let p : {x // x ∈ edgeChoiceSpace s} → Prop :=
    fun choice => edgeChoiceSurvives s choice.1
  let f : {x // x ∈ edgeChoiceSpace s} → ℝ :=
    fun choice =>
      if hsurvive : edgeChoiceSurvives s choice.1 then
        survivalEventProb steps (stateAfterSurvivingChoice s choice hsurvive)
      else 0
  have hsum_raw :
      ((S.filter p).card : ℝ) * B ≤
        ∑ choice ∈ S, if p choice then f choice else 0 := by
    refine card_mul_le_sum_ite_of_lower_bound S p f ?_
    intro choice _hchoice hsurvive
    simpa [f, p, hsurvive] using hind choice hsurvive
  have hsum :
      ((S.filter p).card : ℝ) * B ≤ ∑ choice ∈ S, f choice := by
    calc
      ((S.filter p).card : ℝ) * B
          ≤ ∑ choice ∈ S, if p choice then f choice else 0 := hsum_raw
      _ = ∑ choice ∈ S, f choice := by
            apply Finset.sum_congr rfl
            intro choice _hchoice
            by_cases hsurvive : p choice
            · simp [f, p, hsurvive]
            · simp [f, p, hsurvive]
  have hden_pos : (0 : ℝ) < ((edgeChoiceSpace s).card : ℝ) := by
    exact_mod_cast hm
  have hdiv :
      (((S.filter p).card : ℝ) * B) / (edgeChoiceSpace s).card ≤
        (∑ choice ∈ S, f choice) / (edgeChoiceSpace s).card :=
    div_le_div_of_nonneg_right hsum (le_of_lt hden_pos)
  have hfilter :
      (S.filter p).card =
        ((edgeChoiceSpace s).filter (edgeChoiceSurvives s)).card := by
    simpa [S, p] using edgeChoice_attach_filter_card s
  calc
    edgeChoiceSurvivalRatio s * B
        = (((S.filter p).card : ℝ) * B) / (edgeChoiceSpace s).card := by
            rw [edgeChoiceSurvivalRatio, hfilter]
            ring
    _ ≤ (∑ choice ∈ S, f choice) / (edgeChoiceSpace s).card := hdiv
    _ = survivalEventProb (steps + 1) s := by
          simp [survivalEventProb_succ, S, f]

lemma edgeChoiceSurvivalRatio_ge_factor
    {α : Type*} [DecidableEq α] (s : State α)
    (hmin : IsMulMinCut s.C) (hcut_pos : 0 < s.C.size)
    (hn : 2 ≤ s.G.vertexCount) :
    (((s.G.vertexCount - 2 : ℕ) : ℝ) / s.G.vertexCount) ≤
      edgeChoiceSurvivalRatio s := by
  have hm : 0 < s.G.edgeCount :=
    lt_of_lt_of_le hcut_pos (cut_size_le_edgeCount s)
  have hbound : s.C.size * s.G.vertexCount ≤ 2 * s.G.edgeCount := by
    refine edge_count_lower_bound s.C.size ?_
    intro v hv
    exact mincut_le_degree s.C hmin hv
  rw [edgeChoiceSurvivalRatio_eq_uniformSurvivalProb,
    uniformSurvivalProb_eq_survivalProb s hm]
  exact survivalProb_ge_factor hn hm hbound

/-- Full recursive survival lower bound for the finite edge-occurrence sampling
model.

This is the direct algorithmic version of Karger's fixed-min-cut survival
argument: condition on the first random edge occurrence, recurse on every
surviving contracted state, and multiply by the one-step lower bound.
-/
theorem survivalEventProb_lower_bound
    {α : Type*} [DecidableEq α] :
    ∀ (n : ℕ) (s : State α),
      IsMulMinCut s.C → 0 < s.C.size → 2 ≤ n →
      s.G.vertexCount = n →
      (2 : ℝ) / (n * (n - 1)) ≤ survivalEventProb (n - 2) s := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro s hmin hcut_pos hn hn0
      by_cases htwo : n = 2
      · subst n
        norm_num [htwo]
      · have hgt : 2 < n := by omega
        have hsteps : n - 2 = (n - 3) + 1 := by omega
        rw [hsteps]
        let B : ℝ :=
          (2 : ℝ) / (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ) - 1))
        have hn1_real_pos : 0 < (((n - 1 : ℕ) : ℝ)) := by
          exact_mod_cast (by omega : 0 < n - 1)
        have hn1m1_real_pos : 0 < (((n - 1 : ℕ) : ℝ) - 1) := by
          have hn1_ge_two : (2 : ℕ) ≤ n - 1 := by omega
          have hn1_ge_two_real : (2 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
            exact_mod_cast hn1_ge_two
          linarith
        have hB_nonneg : 0 ≤ B := by
          dsimp [B]
          positivity
        have hspace_pos : 0 < (edgeChoiceSpace s).card := by
          have hm_edges : 0 < s.G.edgeCount :=
            lt_of_lt_of_le hcut_pos (cut_size_le_edgeCount s)
          simpa [edgeChoiceSpace_card] using hm_edges
        have hstep_prob :
            edgeChoiceSurvivalRatio s * B ≤
              survivalEventProb ((n - 3) + 1) s := by
          refine survivalEventProb_step_lower_bound s (n - 3) hspace_pos ?_
          intro choice hsurvive
          let t : State α := stateAfterSurvivingChoice s choice hsurvive
          have hstep : SurvivingStep s t :=
            stateAfterSurvivingChoice_step s choice hsurvive
          have hmin_t : IsMulMinCut t.C :=
            survivingStep_mincut hstep hmin
          have hsize : t.C.size = s.C.size :=
            survivingStep_cut_size_eq hstep
          have hcut_pos_t : 0 < t.C.size := by
            rw [hsize]
            exact hcut_pos
          have hn_t : 2 ≤ n - 1 := by omega
          have hvc_t : t.G.vertexCount = n - 1 := by
            have hvc := survivingStep_vertexCount_eq hstep
            rw [hn0] at hvc
            simpa using hvc
          have hrec :=
            ih (n - 1) (by omega) t hmin_t hcut_pos_t hn_t hvc_t
          have hsteps_t : n - 1 - 2 = n - 3 := by omega
          simpa [B, t, hsteps_t] using hrec
        have hratio :
            (((n - 2 : ℕ) : ℝ) / n) ≤ edgeChoiceSurvivalRatio s := by
          have h :=
            edgeChoiceSurvivalRatio_ge_factor s hmin hcut_pos
              (by simpa [hn0] using hn)
          simpa [hn0] using h
        have halg :
            (((n - 2 : ℕ) : ℝ) / n) * B =
              (2 : ℝ) / (n * (n - 1)) := by
          dsimp [B]
          have hn1_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ n)]
            norm_num
          have hn2_cast :
              ((n - 2 : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) - 1 := by
            have hleft : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
              rw [Nat.cast_sub (by omega : 2 ≤ n)]
              norm_num
            rw [hleft, hn1_cast]
            ring
          have hn_ne : (n : ℝ) ≠ 0 := by
            exact_mod_cast (by omega : n ≠ 0)
          have hn1_ne : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast (by omega : n - 1 ≠ 0)
          have hn1m1_ne : (((n - 1 : ℕ) : ℝ) - 1) ≠ 0 := by
            linarith
          rw [hn2_cast]
          field_simp [hn_ne, hn1_ne, hn1m1_ne]
          rw [hn1_cast]
          have hnm1_ne' : (n : ℝ) - 1 ≠ 0 := by
            linarith
          exact (div_self hnm1_ne').symm
        calc
          (2 : ℝ) / (n * (n - 1))
              = (((n - 2 : ℕ) : ℝ) / n) * B := halg.symm
          _ ≤ edgeChoiceSurvivalRatio s * B :=
                mul_le_mul_of_nonneg_right hratio hB_nonneg
          _ ≤ survivalEventProb ((n - 3) + 1) s := hstep_prob

theorem survivalEventProb_initial_lower_bound
    {α : Type*} [DecidableEq α] (s : State α)
    (hmin : IsMulMinCut s.C) (hcut_pos : 0 < s.C.size)
    (hn : 2 ≤ s.G.vertexCount) :
    (2 : ℝ) / (s.G.vertexCount * (s.G.vertexCount - 1)) ≤
      survivalEventProb (s.G.vertexCount - 2) s := by
  exact survivalEventProb_lower_bound s.G.vertexCount s hmin hcut_pos hn rfl

/-- Human-facing name for the fixed min-cut survival probability theorem. -/
theorem fixed_mincut_survival_probability_lower_bound
    {α : Type*} [DecidableEq α] (s : State α)
    (hmin : IsMulMinCut s.C) (hcut_pos : 0 < s.C.size)
    (hn : 2 ≤ s.G.vertexCount) :
    (2 : ℝ) / (s.G.vertexCount * (s.G.vertexCount - 1)) ≤
      survivalEventProb (s.G.vertexCount - 2) s :=
  survivalEventProb_initial_lower_bound s hmin hcut_pos hn

/-! ## Graph-Only Algorithm Traces -/

/-- The finite edge-occurrence choice space for the graph-only algorithm.

This is the same occurrence space as `edgeChoiceSpace`, but without mentioning
a distinguished cut.
-/
noncomputable def graphChoiceSpace {α : Type*} [DecidableEq α]
    (G : Multigraph α) : Finset (Sym2 α × ℕ) :=
  G.edges.toEnumFinset

lemma graphChoiceSpace_eq_edgeChoiceSpace
    {α : Type*} [DecidableEq α] (s : State α) :
    graphChoiceSpace s.G = edgeChoiceSpace s := rfl

lemma graphChoice_mem_edges {α : Type*} [DecidableEq α]
    (G : Multigraph α) (choice : {x // x ∈ graphChoiceSpace G}) :
    choice.1.1 ∈ G.edges := by
  exact Multiset.mem_of_mem_toEnumFinset (by
    simpa [graphChoiceSpace] using choice.2)

/-- Contract the graph along an arbitrary sampled edge occurrence. -/
noncomputable def graphAfterChoice {α : Type*} [DecidableEq α]
    (G : Multigraph α) (choice : {x // x ∈ graphChoiceSpace G}) :
    Multigraph α :=
  G.contract choice.1.1 (graphChoice_mem_edges G choice)

lemma graphAfterChoice_vertexCount_eq
    {α : Type*} [DecidableEq α] (G : Multigraph α)
    (choice : {x // x ∈ graphChoiceSpace G}) :
    (graphAfterChoice G choice).vertexCount = G.vertexCount - 1 := by
  have hloopless : ¬ choice.1.1.IsDiag :=
    G.loopless choice.1.1 (graphChoice_mem_edges G choice)
  simpa [graphAfterChoice] using
    contract_vertex_count G choice.1.1 (graphChoice_mem_edges G choice) hloopless

lemma stateAfterSurvivingChoice_graph_eq
    {α : Type*} [DecidableEq α] (s : State α)
    (choice : {x // x ∈ edgeChoiceSpace s})
    (hsurvive : edgeChoiceSurvives s choice.1) :
    (stateAfterSurvivingChoice s choice hsurvive).G =
      graphAfterChoice s.G
        (⟨choice.1, by simpa [graphChoiceSpace_eq_edgeChoiceSpace s] using choice.2⟩ :
          {x // x ∈ graphChoiceSpace s.G}) := by
  rfl

/-- Nondeterministic graph-only executions of Karger's contraction loop.

`KargerGraphRun steps G H` means `H` can be reached from `G` by `steps`
successive arbitrary edge-occurrence contractions. This layer intentionally
does not track the distinguished cut; it represents the actual graph evolution
of the algorithm.
-/
inductive KargerGraphRun {α : Type*} [DecidableEq α] :
    ℕ → Multigraph α → Multigraph α → Prop
  | nil (G : Multigraph α) : KargerGraphRun 0 G G
  | cons {steps : ℕ} {G H : Multigraph α}
      (run : KargerGraphRun steps G H)
      (choice : {x // x ∈ graphChoiceSpace H}) :
      KargerGraphRun (steps + 1) G (graphAfterChoice H choice)

lemma kargerGraphRun_vertexCount_eq
    {α : Type*} [DecidableEq α] {steps : ℕ}
    {G H : Multigraph α} (run : KargerGraphRun steps G H) :
    H.vertexCount = G.vertexCount - steps := by
  induction run with
  | nil G =>
      simp
  | cons run choice ih =>
      rw [graphAfterChoice_vertexCount_eq, ih]
      omega

lemma kargerGraphRun_full_vertexCount_eq_two
    {α : Type*} [DecidableEq α] {G H : Multigraph α}
    (run : KargerGraphRun (G.vertexCount - 2) G H)
    (hn : 2 ≤ G.vertexCount) :
    H.vertexCount = 2 := by
  rw [kargerGraphRun_vertexCount_eq run]
  omega

lemma kargerGraphRun_full_output
    {α : Type*} [DecidableEq α] {G H : Multigraph α}
    (run : KargerGraphRun (G.vertexCount - 2) G H)
    (hn : 2 ≤ G.vertexCount) :
    KargerOutput H := by
  exact kargerGraphRun_full_vertexCount_eq_two run hn

lemma choice_mem_graphChoiceSpace_of_edge_mem
    {α : Type*} [DecidableEq α] {G : Multigraph α}
    {e : Sym2 α} (he : e ∈ G.edges) :
    (e, 0) ∈ graphChoiceSpace G := by
  have hcount : 0 < G.edges.count e := Multiset.count_pos.mpr he
  rw [graphChoiceSpace, Multiset.mem_toEnumFinset]
  exact hcount

lemma survivingStep_graphChoice
    {α : Type*} [DecidableEq α] {s t : State α}
    (hstep : SurvivingStep s t) :
    ∃ choice : {x // x ∈ graphChoiceSpace s.G},
      t.G = graphAfterChoice s.G choice := by
  rcases hstep with ⟨e, he, hsurvive, rfl⟩
  let choice : {x // x ∈ graphChoiceSpace s.G} :=
    ⟨(e, 0), choice_mem_graphChoiceSpace_of_edge_mem he⟩
  refine ⟨choice, ?_⟩
  rfl

lemma survivingRun_graphRun
    {α : Type*} [DecidableEq α] {steps : ℕ} {s t : State α}
    (run : SurvivingRun steps s t) :
    KargerGraphRun steps s.G t.G := by
  induction run with
  | nil s =>
      exact KargerGraphRun.nil s.G
  | cons run hstep ih =>
      rcases survivingStep_graphChoice hstep with ⟨choice, hchoice⟩
      rw [hchoice]
      exact KargerGraphRun.cons ih choice

lemma survivingRun_full_output
    {α : Type*} [DecidableEq α] {s t : State α}
    (run : SurvivingRun (s.G.vertexCount - 2) s t)
    (hn : 2 ≤ s.G.vertexCount) :
    KargerOutput t.G := by
  exact kargerGraphRun_full_output (survivingRun_graphRun run) hn

/-- Explicit adaptive graph trace for the algorithm.

The choice type here depends on the graph present at the current step, matching
the adaptive nature of the contraction process.
-/
structure KargerGraphTrace (α : Type*) [DecidableEq α] (steps : ℕ) where
  graph : ℕ → Multigraph α
  choice : ∀ i, i < steps → {x // x ∈ graphChoiceSpace (graph i)}
  step : ∀ i, (hi : i < steps) →
    graph (i + 1) = graphAfterChoice (graph i) (choice i hi)

lemma kargerGraphTrace_prefix_run
    {α : Type*} [DecidableEq α] {steps i : ℕ}
    (T : KargerGraphTrace α steps) (hi : i ≤ steps) :
    KargerGraphRun i (T.graph 0) (T.graph i) := by
  induction i with
  | zero =>
      simpa using KargerGraphRun.nil (T.graph 0)
  | succ i ih =>
      have hi_steps : i < steps := Nat.lt_of_succ_le hi
      have hi_le : i ≤ steps := Nat.le_of_lt hi_steps
      have hrun :
          KargerGraphRun (i + 1) (T.graph 0)
            (graphAfterChoice (T.graph i) (T.choice i hi_steps)) :=
        KargerGraphRun.cons (ih hi_le) (T.choice i hi_steps)
      simpa [Nat.succ_eq_add_one, T.step i hi_steps] using hrun

lemma kargerGraphTrace_vertexCount_eq
    {α : Type*} [DecidableEq α] {steps i : ℕ}
    (T : KargerGraphTrace α steps) (hi : i ≤ steps) :
    (T.graph i).vertexCount = (T.graph 0).vertexCount - i := by
  exact kargerGraphRun_vertexCount_eq (kargerGraphTrace_prefix_run T hi)

lemma kargerGraphTrace_full_output
    {α : Type*} [DecidableEq α] {n : ℕ}
    (T : KargerGraphTrace α (n - 2))
    (hn : 2 ≤ n) (hn0 : (T.graph 0).vertexCount = n) :
    KargerOutput (T.graph (n - 2)) := by
  have hvc := kargerGraphTrace_vertexCount_eq T (le_rfl)
  rw [hn0] at hvc
  dsimp [KargerOutput]
  omega

/-- Human-facing name for graph-trace termination. -/
theorem adaptive_karger_trace_outputs_two_vertices
    {α : Type*} [DecidableEq α] {n : ℕ}
    (T : KargerGraphTrace α (n - 2))
    (hn : 2 ≤ n) (hn0 : (T.graph 0).vertexCount = n) :
    KargerOutput (T.graph (n - 2)) :=
  kargerGraphTrace_full_output T hn hn0

/-- Top-level wrapper for the two algorithmic facts established in this trace
file: the adaptive recursive sampling semantics has the Karger survival lower
bound, and every adaptive graph trace of `n - 2` contractions terminates with a
two-vertex output graph.
-/
theorem karger_algorithmic_trace_summary
    {α : Type*} [DecidableEq α] (s : State α)
    (hmin : IsMulMinCut s.C) (hcut_pos : 0 < s.C.size)
    (hn : 2 ≤ s.G.vertexCount) :
    (2 : ℝ) / (s.G.vertexCount * (s.G.vertexCount - 1)) ≤
        survivalEventProb (s.G.vertexCount - 2) s ∧
      ∀ T : KargerGraphTrace α (s.G.vertexCount - 2),
        T.graph 0 = s.G → KargerOutput (T.graph (s.G.vertexCount - 2)) := by
  refine ⟨survivalEventProb_initial_lower_bound s hmin hcut_pos hn, ?_⟩
  intro T hT0
  refine kargerGraphTrace_full_output (n := s.G.vertexCount) T hn ?_
  rw [hT0]

/-- Human-facing main theorem for this trace file. -/
theorem adaptive_karger_trace_main
    {α : Type*} [DecidableEq α] (s : State α)
    (hmin : IsMulMinCut s.C) (hcut_pos : 0 < s.C.size)
    (hn : 2 ≤ s.G.vertexCount) :
    (2 : ℝ) / (s.G.vertexCount * (s.G.vertexCount - 1)) ≤
        survivalEventProb (s.G.vertexCount - 2) s ∧
      ∀ T : KargerGraphTrace α (s.G.vertexCount - 2),
        T.graph 0 = s.G → KargerOutput (T.graph (s.G.vertexCount - 2)) :=
  karger_algorithmic_trace_summary s hmin hcut_pos hn

/-! ## Product-Style Surviving Trace Proof

This section keeps the earlier product/telescoping version of the argument.
It is useful for comparing the formalization against the textbook proof, but
the recursive theorem above is the main algorithmic probability statement.
-/

/-- An indexed trace of `steps` surviving contractions.

This is the product-friendly version of `SurvivingRun`: it exposes the state
at every index, so finite products can refer to the graph present at step `i`.
-/
structure SurvivingTrace (α : Type*) [DecidableEq α] (steps : ℕ) where
  state : ℕ → State α
  step : ∀ i, i < steps → SurvivingStep (state i) (state (i + 1))

noncomputable def survivingTrace_toGraphTrace
    {α : Type*} [DecidableEq α] {steps : ℕ}
    (T : SurvivingTrace α steps) : KargerGraphTrace α steps where
  graph := fun i => (T.state i).G
  choice := fun i hi => Classical.choose (survivingStep_graphChoice (T.step i hi))
  step := fun i hi => Classical.choose_spec (survivingStep_graphChoice (T.step i hi))

lemma survivingTrace_prefix_run {α : Type*} [DecidableEq α]
    {steps i : ℕ} (T : SurvivingTrace α steps) (hi : i ≤ steps) :
    SurvivingRun i (T.state 0) (T.state i) := by
  induction i with
  | zero =>
      simpa using SurvivingRun.nil (T.state 0)
  | succ i ih =>
      have hi_steps : i < steps := Nat.lt_of_succ_le hi
      have hi_le : i ≤ steps := Nat.le_of_lt hi_steps
      simpa [Nat.succ_eq_add_one] using
        SurvivingRun.cons (ih hi_le) (T.step i hi_steps)

lemma survivingTrace_vertexCount_eq {α : Type*} [DecidableEq α]
    {steps i : ℕ} (T : SurvivingTrace α steps) (hi : i ≤ steps) :
    (T.state i).G.vertexCount = (T.state 0).G.vertexCount - i := by
  exact survivingRun_vertexCount_eq (survivingTrace_prefix_run T hi)

lemma survivingTrace_survivalProb_ge_factor {α : Type*} [DecidableEq α]
    {steps i : ℕ} (T : SurvivingTrace α steps)
    (hmin : IsMulMinCut (T.state 0).C) (hi : i < steps)
    (hn : 2 ≤ (T.state i).G.vertexCount) :
    (((T.state i).G.vertexCount - 2 : ℕ) : ℝ) / (T.state i).G.vertexCount ≤
      survivalProb (T.state 0).C.size (T.state i).G.edgeCount := by
  exact survivingRun_survivalProb_ge_factor
    (survivingTrace_prefix_run T (Nat.le_of_lt hi)) (T.step i hi) hmin hn

lemma survivingTrace_factor_product_le_survival_product
    {α : Type*} [DecidableEq α] {steps : ℕ}
    (T : SurvivingTrace α steps) (hmin : IsMulMinCut (T.state 0).C)
    (hn : ∀ i, i < steps → 2 ≤ (T.state i).G.vertexCount) :
    Finset.prod (Finset.range steps)
        (fun i => (((T.state i).G.vertexCount - 2 : ℕ) : ℝ) / (T.state i).G.vertexCount) ≤
      Finset.prod (Finset.range steps)
        (fun i => survivalProb (T.state 0).C.size (T.state i).G.edgeCount) := by
  refine Finset.prod_le_prod ?nonneg ?le_step
  · intro i hi
    positivity
  · intro i hi
    exact survivingTrace_survivalProb_ge_factor T hmin
      (Finset.mem_range.mp hi) (hn i (Finset.mem_range.mp hi))

lemma survivingTrace_factor_product_eq_telescope
    {α : Type*} [DecidableEq α] {steps n : ℕ}
    (T : SurvivingTrace α steps) (hsteps : steps = n - 2)
    (hn0 : (T.state 0).G.vertexCount = n) :
    Finset.prod (Finset.range steps)
        (fun i => (((T.state i).G.vertexCount - 2 : ℕ) : ℝ) / (T.state i).G.vertexCount) =
      Finset.prod (Finset.range (n - 2))
        (fun i => ((n : ℝ) - i - 2) / ((n : ℝ) - i)) := by
  subst hsteps
  apply Finset.prod_congr rfl
  intro i hi
  have hi_lt : i < n - 2 := Finset.mem_range.mp hi
  have hi_le_steps : i ≤ n - 2 := Nat.le_of_lt hi_lt
  have hi_le_n : i ≤ n := by omega
  have hi_two : 2 ≤ n - i := by omega
  have hvc :
      (T.state i).G.vertexCount = n - i := by
    have h := survivingTrace_vertexCount_eq T hi_le_steps
    simpa [hn0] using h
  have hden : ((n - i : ℕ) : ℝ) = (n : ℝ) - i := by
    rw [Nat.cast_sub hi_le_n]
  have hnum : (((n - i) - 2 : ℕ) : ℝ) = (n : ℝ) - i - 2 := by
    rw [Nat.cast_sub hi_two, hden]
    norm_num
  simp [hvc, hden, hnum]

/-- Product-level trace lower bound.

This is the next bridge after the one-step lemma: multiply the per-step
survival lower bounds along an indexed surviving trace, then use the same
telescoping product as the combinatorial proof.
-/
theorem survivingTrace_product_survival_lower_bound
    {α : Type*} [DecidableEq α] {n : ℕ}
    (T : SurvivingTrace α (n - 2))
    (hmin : IsMulMinCut (T.state 0).C)
    (hn : 2 ≤ n)
    (hn0 : (T.state 0).G.vertexCount = n)
    (hn_steps : ∀ i, i < n - 2 → 2 ≤ (T.state i).G.vertexCount) :
    (2 : ℝ) / (n * (n - 1)) ≤
      Finset.prod (Finset.range (n - 2))
        (fun i => survivalProb (T.state 0).C.size (T.state i).G.edgeCount) := by
  have hprod :=
    survivingTrace_factor_product_le_survival_product T hmin hn_steps
  have htelescope :
      Finset.prod (Finset.range (n - 2))
          (fun i => (((T.state i).G.vertexCount - 2 : ℕ) : ℝ) /
            (T.state i).G.vertexCount) =
        (2 : ℝ) / (n * (n - 1)) := by
    rw [survivingTrace_factor_product_eq_telescope T rfl hn0]
    exact telescope_prod n hn
  calc
    (2 : ℝ) / (n * (n - 1))
        = Finset.prod (Finset.range (n - 2))
            (fun i => (((T.state i).G.vertexCount - 2 : ℕ) : ℝ) /
              (T.state i).G.vertexCount) := htelescope.symm
    _ ≤ Finset.prod (Finset.range (n - 2))
        (fun i => survivalProb (T.state 0).C.size (T.state i).G.edgeCount) := hprod

/-- Product of concrete conditional survival probabilities along an indexed trace. -/
noncomputable def survivingTraceUniformSurvivalProduct
    {α : Type*} [DecidableEq α] {steps : ℕ}
    (T : SurvivingTrace α steps) : ℝ :=
  Finset.prod (Finset.range steps) fun i => uniformSurvivalProb (T.state i)

lemma survivingTrace_uniform_product_eq_survival_product
    {α : Type*} [DecidableEq α] {steps : ℕ}
    (T : SurvivingTrace α steps) :
    survivingTraceUniformSurvivalProduct T =
      Finset.prod (Finset.range steps)
        (fun i => survivalProb (T.state i).C.size (T.state i).G.edgeCount) := by
  unfold survivingTraceUniformSurvivalProduct
  apply Finset.prod_congr rfl
  intro i hi
  exact uniformSurvivalProb_eq_survivalProb (T.state i)
    (survivingStep_edgeCount_pos (T.step i (Finset.mem_range.mp hi)))

lemma survivingTrace_uniform_product_eq_initial_cut_survival_product
    {α : Type*} [DecidableEq α] {steps : ℕ}
    (T : SurvivingTrace α steps) :
    survivingTraceUniformSurvivalProduct T =
      Finset.prod (Finset.range steps)
        (fun i => survivalProb (T.state 0).C.size (T.state i).G.edgeCount) := by
  rw [survivingTrace_uniform_product_eq_survival_product T]
  apply Finset.prod_congr rfl
  intro i hi
  have hrun : SurvivingRun i (T.state 0) (T.state i) :=
    survivingTrace_prefix_run T (Nat.le_of_lt (Finset.mem_range.mp hi))
  have hsize : (T.state i).C.size = (T.state 0).C.size :=
    survivingRun_cut_size_eq hrun
  simp [hsize]

/-- Product-level lower bound stated using the concrete uniform edge-choice
probabilities. -/
theorem survivingTrace_uniform_survival_product_lower_bound
    {α : Type*} [DecidableEq α] {n : ℕ}
    (T : SurvivingTrace α (n - 2))
    (hmin : IsMulMinCut (T.state 0).C)
    (hn : 2 ≤ n)
    (hn0 : (T.state 0).G.vertexCount = n)
    (hn_steps : ∀ i, i < n - 2 → 2 ≤ (T.state i).G.vertexCount) :
    (2 : ℝ) / (n * (n - 1)) ≤ survivingTraceUniformSurvivalProduct T := by
  have habstract :=
    survivingTrace_product_survival_lower_bound T hmin hn hn0 hn_steps
  rw [survivingTrace_uniform_product_eq_initial_cut_survival_product T]
  exact habstract

/-- Product of concrete finite sample-space survival ratios along a trace. -/
noncomputable def survivingTraceEdgeChoiceSurvivalProduct
    {α : Type*} [DecidableEq α] {steps : ℕ}
    (T : SurvivingTrace α steps) : ℝ :=
  Finset.prod (Finset.range steps) fun i => edgeChoiceSurvivalRatio (T.state i)

lemma survivingTrace_edgeChoice_product_eq_uniform_product
    {α : Type*} [DecidableEq α] {steps : ℕ}
    (T : SurvivingTrace α steps) :
    survivingTraceEdgeChoiceSurvivalProduct T =
      survivingTraceUniformSurvivalProduct T := by
  unfold survivingTraceEdgeChoiceSurvivalProduct survivingTraceUniformSurvivalProduct
  apply Finset.prod_congr rfl
  intro i _hi
  exact edgeChoiceSurvivalRatio_eq_uniformSurvivalProb (T.state i)

/-- The same product lower bound, stated only in terms of finite uniform
edge-choice sample-space ratios. -/
theorem survivingTrace_edgeChoice_survival_product_lower_bound
    {α : Type*} [DecidableEq α] {n : ℕ}
    (T : SurvivingTrace α (n - 2))
    (hmin : IsMulMinCut (T.state 0).C)
    (hn : 2 ≤ n)
    (hn0 : (T.state 0).G.vertexCount = n)
    (hn_steps : ∀ i, i < n - 2 → 2 ≤ (T.state i).G.vertexCount) :
    (2 : ℝ) / (n * (n - 1)) ≤ survivingTraceEdgeChoiceSurvivalProduct T := by
  rw [survivingTrace_edgeChoice_product_eq_uniform_product T]
  exact survivingTrace_uniform_survival_product_lower_bound T hmin hn hn0 hn_steps

end KargerTrace
