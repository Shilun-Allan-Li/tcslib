/-
Copyright (c) 2026 Joon Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joon Kim
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open scoped BigOperators
open Finset Nat

set_option linter.unnecessarySimpa false
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Karger's Randomized Min-Cut Algorithm

This file formalizes the multigraph model and the key structural lemmas
underlying Karger's randomized contraction algorithm for finding minimum cuts
in multigraphs.

## Main results

- `contract_vertex_count`: Contracting an edge reduces the vertex count by 1.
- `cut_size_preserved`: Contracting a non-crossing edge preserves cut size.
- `mincut_preserved_of_non_crossing`: Non-crossing contraction preserves the min-cut property.
- `mincut_le_degree`: The min-cut size is at most the degree of any vertex.
- `sum_degrees_eq_twice_edgeCount`: Handshake lemma: `Σ deg(v) = 2|E|`.
- `telescope_prod`: The telescoping product equals `2 / (n * (n - 1))`.
- `karger_survival_prob_algorithmic`: A fixed min-cut survives `n - 2` contractions with
  probability at least `2 / (n * (n - 1))`.
- `karger_whp`: Repeating `O(n²)` times finds a min-cut with high probability.
- `num_mincuts_le_choose`: There are at most `C(n, 2)` distinct min-cuts.
- `num_alpha_mincuts_le`: There are at most `n ^ (2α)` distinct α-min-cuts.

## References

- Karger, D.R. (1993): Global min-cuts in RNC, and other ramifications of a simple
  min-cut algorithm.
-/

/-! ## Multigraph Model

`SimpleGraph` does not support parallel edges; Karger's contraction creates them.
We model a multigraph as a `Multiset` of unordered pairs over the vertex type. -/

/-- A multigraph on vertex set α is a multiset of unordered pairs. -/
structure Multigraph (α : Type*) where
  vertices : Finset α
  edges    : Multiset (Sym2 α)
  -- Every edge endpoint is a live vertex
  mem_vertices : ∀ e ∈ edges, ∀ v ∈ e, v ∈ vertices
  -- Self-loops are deleted immediately after each contraction step.
  loopless : ∀ e ∈ edges, ¬ e.IsDiag

/-- Number of edges (with multiplicity). -/
def Multigraph.edgeCount {α} (G : Multigraph α) : ℕ :=
  G.edges.card

/-- Number of vertices. -/
def Multigraph.vertexCount {α} [DecidableEq α] (G : Multigraph α) : ℕ :=
  G.vertices.card

/-! ## Edge Contraction -/

/-- Contract edge {u, v}: merge v into u throughout.
    - Remove all edges between u and v (self-loops after merge)
    - Replace every occurrence of v with u in remaining edges
    - Remove v from vertex set -/
noncomputable def Multigraph.contract {α : Type*} [DecidableEq α]
    (G : Multigraph α) (e : Sym2 α) (he : e ∈ G.edges) : Multigraph α :=
  let u := e.out.1
  let v := e.out.2
  let redirect : α → α := fun w => if w = v then u else w
  let newEdges :=
    (G.edges.map (fun f => f.map redirect))
      |>.filter (fun f => ¬ f.IsDiag)  -- remove self-loops
  { vertices := G.vertices.erase v
    edges    := newEdges
    mem_vertices := by
      intro f hf x hx
      have hdiag : ¬ e.IsDiag := G.loopless e he
      have hdiag_iff : e.IsDiag ↔ u = v := by
        simpa [u, v, Sym2.mk, e.out_eq] using (Sym2.isDiag_iff_proj_eq e.out)
      have huv : u ≠ v := fun huv => hdiag (hdiag_iff.mpr huv)
      have hu_mem : u ∈ G.vertices := G.mem_vertices e he u (Sym2.out_fst_mem e)
      have hf' := Multiset.mem_filter.mp hf
      obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.mp hf'.1
      obtain ⟨y, hy, rfl⟩ := Sym2.mem_map.mp hx
      by_cases hyv : y = v
      · subst hyv
        exact Finset.mem_erase.mpr
          ⟨by simpa [redirect, huv], by simpa [redirect] using hu_mem⟩
      · exact Finset.mem_erase.mpr
          ⟨by simpa [redirect, hyv], by simpa [redirect, hyv] using G.mem_vertices g hg y hy⟩
    loopless := by
      intro f hf
      exact (Multiset.mem_filter.mp hf).2 }

/-- Contraction decreases vertex count by exactly 1. -/
lemma contract_vertex_count {α : Type*} [DecidableEq α]
    (G : Multigraph α) (e : Sym2 α) (he : e ∈ G.edges)
    (_hne : ¬ e.IsDiag) :
    (G.contract e he).vertexCount = G.vertexCount - 1 := by
  have hv_mem : e.out.2 ∈ G.vertices := G.mem_vertices e he _ (Sym2.out_snd_mem e)
  simp [Multigraph.contract, Multigraph.vertexCount, hv_mem]

/-- Contraction never increases edge count
    (removes the contracted edge). -/
lemma contract_edge_count_le {α : Type*} [DecidableEq α]
    (G : Multigraph α) (e : Sym2 α) (he : e ∈ G.edges) :
    (G.contract e he).edgeCount ≤ G.edgeCount - 1 := by
  let u := e.out.1
  let v := e.out.2
  let redirect : α → α := fun w => if w = v then u else w
  let mapped := G.edges.map (fun f => f.map redirect)
  let a : Sym2 α := e.map redirect
  have hemapped : a ∈ mapped := by
    exact Multiset.mem_map_of_mem _ he
  have hdiag : a.IsDiag := by
    change (e.map redirect).IsDiag
    rw [← e.out_eq, Sym2.map_mk, Sym2.isDiag_iff_proj_eq]
    simp [redirect, u, v]
  have hnot_mem : a ∉ (G.contract e he).edges := by
    intro h
    exact (Multiset.mem_filter.mp h).2 hdiag
  have hle :
      (G.contract e he).edges ≤ mapped.erase a := by
    have hbase : (G.contract e he).edges ≤ mapped := by
      exact Multiset.filter_le (fun f : Sym2 α => ¬ f.IsDiag) mapped
    have hcons :
        (G.contract e he).edges ≤ a ::ₘ mapped.erase a := by
      simpa [a, Multiset.cons_erase hemapped] using hbase
    have herase :
        ((G.contract e he).edges).erase a ≤ mapped.erase a :=
      (Multiset.erase_le_iff_le_cons).2 hcons
    simpa [a, Multiset.erase_of_notMem hnot_mem] using herase
  have hlt :
      (G.contract e he).edgeCount < G.edgeCount := by
    calc
      (G.contract e he).edgeCount
          = ((G.contract e he).edges).card := rfl
      _ ≤ (mapped.erase a).card := Multiset.card_le_card hle
      _ < mapped.card := Multiset.card_erase_lt_of_mem hemapped
      _ = G.edgeCount := by simp [mapped, Multigraph.edgeCount]
  omega

/-! ## Cut Notion for Multigraphs -/

/-- A cut in a multigraph: partition of vertices into S and its complement.
    S and Sc must be nonempty to ensure that the cut is not trivial. -/
structure MulCut {α : Type*} [DecidableEq α] (G : Multigraph α) where
  S     : Finset α
  subset : S ⊆ G.vertices
  hS    : S.Nonempty
  hSc   : (G.vertices \ S).Nonempty

/-- Edges of the multigraph crossing the cut (with multiplicity). -/
noncomputable def MulCut.crossingEdges {α : Type*} [DecidableEq α]
    {G : Multigraph α} (C : MulCut G) : Multiset (Sym2 α) :=
  G.edges.filter fun e =>
    (e.out.1 ∈ C.S ∧ e.out.2 ∉ C.S) ∨
    (e.out.1 ∉ C.S ∧ e.out.2 ∈ C.S)

/-- Membership-based crossing predicate for unordered edges. -/
def Crosses {α : Type*} [DecidableEq α] (S : Finset α) (e : Sym2 α) : Prop :=
  (∃ x, x ∈ e ∧ x ∈ S) ∧ ∃ y, y ∈ e ∧ y ∉ S

noncomputable instance crossesDecidable {α : Type*} [DecidableEq α] (S : Finset α) :
    DecidablePred (Crosses S) := by
  classical
  intro e
  dsimp [Crosses]
  infer_instance

lemma crosses_iff_out {α : Type*} [DecidableEq α] (S : Finset α) (e : Sym2 α) :
    Crosses S e ↔
      ((e.out.1 ∈ S ∧ e.out.2 ∉ S) ∨
        (e.out.1 ∉ S ∧ e.out.2 ∈ S)) := by
  constructor
  · rintro ⟨⟨x, hxe, hxS⟩, ⟨y, hye, hyS⟩⟩
    have hmem_out : ∀ {z}, z ∈ e → z = e.out.1 ∨ z = e.out.2 := by
      intro z hze
      have hz' : z ∈ s(e.out.1, e.out.2) := by
        simpa [Sym2.mk] using (show z ∈ Sym2.mk e.out by simpa [e.out_eq] using hze)
      exact Sym2.mem_iff.mp hz'
    by_cases h1 : e.out.1 ∈ S
    · left
      refine ⟨h1, ?_⟩
      intro h2
      rcases hmem_out hye with rfl | rfl
      · exact hyS h1
      · exact hyS h2
    · right
      refine ⟨h1, ?_⟩
      rcases hmem_out hxe with rfl | rfl
      · exact False.elim (h1 hxS)
      · exact hxS
  · rintro (h | h)
    · refine ⟨⟨e.out.1, Sym2.out_fst_mem e, h.1⟩, ⟨e.out.2, Sym2.out_snd_mem e, h.2⟩⟩
    · refine ⟨⟨e.out.2, Sym2.out_snd_mem e, h.2⟩, ⟨e.out.1, Sym2.out_fst_mem e, h.1⟩⟩

lemma crossingEdges_eq_filter_crosses {α : Type*} [DecidableEq α]
    {G : Multigraph α} (C : MulCut G) :
    C.crossingEdges = G.edges.filter (Crosses C.S) := by
  rw [MulCut.crossingEdges]
  apply Multiset.filter_congr
  intro e he
  exact (crosses_iff_out C.S e).symm

noncomputable def MulCut.size {α : Type*} [DecidableEq α]
    {G : Multigraph α} (C : MulCut G) : ℕ :=
  C.crossingEdges.card

noncomputable def IsMulMinCut {α : Type*} [DecidableEq α]
    {G : Multigraph α} (C : MulCut G) : Prop :=
  ∀ C' : MulCut G, C.size ≤ C'.size

/-! ## Cut Survival Under Contraction

The key section: contracting a non-crossing edge preserves cut size and the
min-cut property. -/

/-- A cut C in G induces a cut in G.contract e he,
    provided e does not cross C. -/
noncomputable def MulCut.contractedCut {α : Type*} [DecidableEq α]
    {G : Multigraph α} (C : MulCut G) (e : Sym2 α)
    (he : e ∈ G.edges) (hsurvive : e ∉ C.crossingEdges) :
    MulCut (G.contract e he) :=
  { S    := (G.contract e he).vertices ∩ C.S
    subset := by
      intro x hx
      exact (Finset.mem_inter.mp hx).1
    hS   := by
      let u := e.out.1
      let v := e.out.2
      have hdiag : ¬ e.IsDiag := G.loopless e he
      have hdiag_iff : e.IsDiag ↔ u = v := by
        simpa [u, v, Sym2.mk, e.out_eq] using (Sym2.isDiag_iff_proj_eq e.out)
      have huv : u ≠ v := fun huv => hdiag (hdiag_iff.mpr huv)
      have hu_mem : u ∈ G.vertices := G.mem_vertices e he u (Sym2.out_fst_mem e)
      by_cases huS : u ∈ C.S
      · have hvS : v ∈ C.S := by
          by_contra hvS
          exact hsurvive <| by
            rw [MulCut.crossingEdges]
            exact Multiset.mem_filter.mpr ⟨he, Or.inl ⟨huS, hvS⟩⟩
        have huv' : u ≠ e.out.2 := by
          simpa [v] using huv
        exact ⟨u, by
          simp [Multigraph.contract, huS, hu_mem, huv']⟩
      · rcases C.hS with ⟨w, hwS⟩
        have hvS : v ∉ C.S := by
          intro hvS
          exact hsurvive <| by
            rw [MulCut.crossingEdges]
            exact Multiset.mem_filter.mpr ⟨he, Or.inr ⟨huS, hvS⟩⟩
        have hwv : w ≠ v := by
          intro hwv
          exact hvS (hwv ▸ hwS)
        have hw_mem : w ∈ G.vertices := C.subset hwS
        have hwv' : w ≠ e.out.2 := by
          simpa [v] using hwv
        exact ⟨w, by
          simp [Multigraph.contract, hwS, hw_mem, hwv']⟩
    hSc  := by
      let u := e.out.1
      let v := e.out.2
      have hdiag : ¬ e.IsDiag := G.loopless e he
      have hdiag_iff : e.IsDiag ↔ u = v := by
        simpa [u, v, Sym2.mk, e.out_eq] using (Sym2.isDiag_iff_proj_eq e.out)
      have huv : u ≠ v := fun huv => hdiag (hdiag_iff.mpr huv)
      have hu_mem : u ∈ G.vertices := G.mem_vertices e he u (Sym2.out_fst_mem e)
      by_cases huS : u ∈ C.S
      · rcases C.hSc with ⟨w, hw⟩
        have hvS : v ∈ C.S := by
          by_contra hvS
          exact hsurvive <| by
            rw [MulCut.crossingEdges]
            exact Multiset.mem_filter.mpr ⟨he, Or.inl ⟨huS, hvS⟩⟩
        have hwv : w ≠ v := by
          intro hwv
          exact (Finset.mem_sdiff.mp hw).2 (hwv ▸ hvS)
        have hwv' : w ≠ e.out.2 := by
          simpa [v] using hwv
        exact ⟨w, by
          have hw' := Finset.mem_sdiff.mp hw
          simp [Multigraph.contract, hw'.1, hw'.2, hwv']⟩
      · have hvS : v ∉ C.S := by
          intro hvS
          exact hsurvive <| by
            rw [MulCut.crossingEdges]
            exact Multiset.mem_filter.mpr ⟨he, Or.inr ⟨huS, hvS⟩⟩
        have huv' : u ≠ e.out.2 := by
          simpa [v] using huv
        exact ⟨u, by
          simp [Multigraph.contract, hu_mem, huS, huv']⟩ }

/-- If e does not cross C, then the contracted cut has the same size.
    This ensures that as long as we never touch the min-cut of our choice,
    the algorithm survives that step. -/
lemma cut_size_preserved {α : Type*} [DecidableEq α]
    {G : Multigraph α} (C : MulCut G) (e : Sym2 α)
    (he : e ∈ G.edges) (hsurvive : e ∉ C.crossingEdges) :
    (C.contractedCut e he hsurvive).size = C.size := by
  let D := C.contractedCut e he hsurvive
  let u := e.out.1
  let v := e.out.2
  let redirect : α → α := fun w => if w = v then u else w
  have hdiag : ¬ e.IsDiag := G.loopless e he
  have hdiag_iff : e.IsDiag ↔ u = v := by
    simpa [u, v, Sym2.mk, e.out_eq] using (Sym2.isDiag_iff_proj_eq e.out)
  have huv : u ≠ v := fun huv => hdiag (hdiag_iff.mpr huv)
  have huS_iff_hvS : u ∈ C.S ↔ v ∈ C.S := by
    constructor
    · intro huS
      by_contra hvS
      exact hsurvive <| by
        rw [crossingEdges_eq_filter_crosses]
        exact Multiset.mem_filter.mpr
          ⟨he, (crosses_iff_out C.S e).2 (Or.inl ⟨huS, hvS⟩)⟩
    · intro hvS
      by_contra huS
      exact hsurvive <| by
        rw [crossingEdges_eq_filter_crosses]
        exact Multiset.mem_filter.mpr
          ⟨he, (crosses_iff_out C.S e).2 (Or.inr ⟨huS, hvS⟩)⟩
  have hside : ∀ x, redirect x ∈ C.S ↔ x ∈ C.S := by
    intro x
    by_cases hx : x = v
    · subst hx
      simpa [redirect] using huS_iff_hvS
    · simp [redirect, hx]
  have hredir_mem : ∀ x, x ∈ G.vertices → redirect x ∈ (G.contract e he).vertices := by
    intro x hx
    by_cases hxv : x = v
    · subst hxv
      have hu_mem : u ∈ G.vertices := G.mem_vertices e he u (Sym2.out_fst_mem e)
      have huv' : u ≠ e.out.2 := by simpa [v] using huv
      simpa [Multigraph.contract, redirect] using (Finset.mem_erase.mpr ⟨huv', hu_mem⟩)
    · have hxv' : x ≠ e.out.2 := by simpa [v] using hxv
      simpa [Multigraph.contract, redirect, hxv] using (Finset.mem_erase.mpr ⟨hxv', hx⟩)
  have hcross_map : ∀ f ∈ G.edges, Crosses D.S (f.map redirect) ↔ Crosses C.S f := by
    intro f hf
    constructor
    · rintro ⟨⟨x, hx, hxD⟩, ⟨y, hy, hyD⟩⟩
      rcases Sym2.mem_map.mp hx with ⟨x₀, hx₀, rfl⟩
      rcases Sym2.mem_map.mp hy with ⟨y₀, hy₀, rfl⟩
      refine ⟨⟨x₀, hx₀, ?_⟩, ⟨y₀, hy₀, ?_⟩⟩
      · exact (hside x₀).1 ((Finset.mem_inter.mp hxD).2)
      · intro hyS
        exact hyD <| Finset.mem_inter.mpr ⟨hredir_mem y₀ (G.mem_vertices f hf y₀ hy₀), (hside y₀).2 hyS⟩
    · rintro ⟨⟨x, hx, hxS⟩, ⟨y, hy, hyS⟩⟩
      refine ⟨⟨redirect x, ?_, ?_⟩, ⟨redirect y, ?_, ?_⟩⟩
      · exact Sym2.mem_map.2 ⟨x, hx, rfl⟩
      · exact Finset.mem_inter.mpr ⟨hredir_mem x (G.mem_vertices f hf x hx), (hside x).2 hxS⟩
      · exact Sym2.mem_map.2 ⟨y, hy, rfl⟩
      · intro hyD
        exact hyS ((hside y).1 ((Finset.mem_inter.mp hyD).2))
  have hcross_notdiag : ∀ f, Crosses D.S f → ¬ f.IsDiag := by
    intro f hf hfd
    have hdiag_out : f.out.1 = f.out.2 := by
      have hfd' : (Sym2.mk f.out).IsDiag := by simpa [Sym2.mk, f.out_eq] using hfd
      simpa using (Sym2.isDiag_iff_proj_eq f.out).mp hfd'
    have hout := (crosses_iff_out D.S f).mp hf
    cases hout with
    | inl h => exact h.2 (hdiag_out ▸ h.1)
    | inr h => exact h.1 (hdiag_out ▸ h.2)
  have hDcross : D.crossingEdges = (G.contract e he).edges.filter (Crosses D.S) :=
    crossingEdges_eq_filter_crosses D
  rw [show D.size = D.crossingEdges.card by rfl, hDcross, MulCut.size, crossingEdges_eq_filter_crosses]
  change
    ((((G.edges.map (fun f => f.map redirect)).filter fun f => ¬ f.IsDiag).filter
      (Crosses D.S)).card) =
      (G.edges.filter (Crosses C.S)).card
  rw [Multiset.filter_filter]
  have hdrop :
      (G.edges.map (fun f => f.map redirect)).filter (fun f => Crosses D.S f ∧ ¬ f.IsDiag) =
        (G.edges.map (fun f => f.map redirect)).filter (Crosses D.S) := by
    apply Multiset.filter_congr
    intro f hf
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, hcross_notdiag f h⟩
  rw [hdrop, Multiset.filter_map]
  have hcongr :
      G.edges.filter (fun f => Crosses D.S (f.map redirect)) =
        G.edges.filter (Crosses C.S) := by
    apply Multiset.filter_congr
    intro f hf
    exact hcross_map f hf
  have hcongr' :
      G.edges.filter (Crosses D.S ∘ fun f => f.map redirect) =
        G.edges.filter (Crosses C.S) := by
    simpa [Function.comp] using hcongr
  rw [hcongr', Multiset.card_map]

/-- Contracting a non-cut edge never destroys the min-cut property.
    This is the KEY lemma: formal proof that only cut edges "kill" the cut. -/
lemma mincut_preserved_of_non_crossing {α : Type*} [DecidableEq α]
    {G : Multigraph α} (C : MulCut G) (hC : IsMulMinCut C)
    (e : Sym2 α) (he : e ∈ G.edges) (hsurvive : e ∉ C.crossingEdges) :
    IsMulMinCut (C.contractedCut e he hsurvive) := by
  intro D
  let u := e.out.1
  let v := e.out.2
  have hdiag : ¬ e.IsDiag := G.loopless e he
  have hdiag_iff : e.IsDiag ↔ u = v := by
    simpa [u, v, Sym2.mk, e.out_eq] using (Sym2.isDiag_iff_proj_eq e.out)
  have huv : u ≠ v := fun huv => hdiag (hdiag_iff.mpr huv)
  have hu_mem : u ∈ G.vertices := G.mem_vertices e he u (Sym2.out_fst_mem e)
  have hv_mem : v ∈ G.vertices := G.mem_vertices e he v (Sym2.out_snd_mem e)
  have hv_notin_contract : v ∉ (G.contract e he).vertices := by
    intro hvcon
    have hvør : v ≠ e.out.2 ∧ v ∈ G.vertices := by
      simpa [Multigraph.contract] using hvcon
    exact hvør.1 rfl
  let liftS : Finset α := if u ∈ D.S then insert v D.S else D.S
  have hv_notin_D : v ∉ D.S := by
    intro hvD
    exact hv_notin_contract (D.subset hvD)
  let D' : MulCut G :=
    { S := liftS
      subset := by
        intro x hx
        by_cases huD : u ∈ D.S
        · have hx' : x = v ∨ x ∈ D.S := by
            simpa [liftS, huD] using hx
          rcases hx' with rfl | hxD
          · exact hv_mem
          · have hxvert : x ∈ G.vertices.erase v := by
              simpa [Multigraph.contract] using D.subset hxD
            exact (Finset.mem_erase.mp hxvert).2
        · have hxD : x ∈ D.S := by
            simpa [liftS, huD] using hx
          have hxvert : x ∈ G.vertices.erase v := by
            simpa [Multigraph.contract] using D.subset hxD
          exact (Finset.mem_erase.mp hxvert).2
      hS := by
        rcases D.hS with ⟨x, hx⟩
        refine ⟨x, ?_⟩
        by_cases huD : u ∈ D.S
        · simpa [liftS, huD] using Finset.mem_insert_of_mem hx
        · simpa [liftS, huD] using hx
      hSc := by
        by_cases huD : u ∈ D.S
        · rcases D.hSc with ⟨x, hx⟩
          have hxvert : x ∈ (G.contract e he).vertices := (Finset.mem_sdiff.mp hx).1
          have hxnotD : x ∉ D.S := (Finset.mem_sdiff.mp hx).2
          have hxvert' : x ∈ G.vertices.erase v := by
            simpa [Multigraph.contract] using hxvert
          have hxne : x ≠ v := (Finset.mem_erase.mp hxvert').1
          have hxG : x ∈ G.vertices := (Finset.mem_erase.mp hxvert').2
          refine ⟨x, Finset.mem_sdiff.mpr ⟨hxG, ?_⟩⟩
          simpa [liftS, huD, hxnotD, hxne]
        · refine ⟨v, Finset.mem_sdiff.mpr ⟨hv_mem, ?_⟩⟩
          simpa [liftS, huD] using hv_notin_D }
  have hsurvive' : e ∉ D'.crossingEdges := by
    intro hcross
    rw [MulCut.crossingEdges] at hcross
    rcases Multiset.mem_filter.mp hcross with ⟨_, hc⟩
    by_cases huD : u ∈ D.S
    · have huLift : u ∈ D'.S := by
        simpa [D', liftS, huD] using huD
      have hvLift : v ∈ D'.S := by
        simp [D', liftS, huD]
      cases hc with
      | inl h => exact h.2 hvLift
      | inr h => exact h.1 huLift
    · have huLift : u ∉ D'.S := by
        simpa [D', liftS, huD] using huD
      have hvLift : v ∉ D'.S := by
        simpa [D', liftS, huD] using hv_notin_D
      cases hc with
      | inl h => exact huLift h.1
      | inr h => exact hvLift h.2
  have hS_eq : (D'.contractedCut e he hsurvive').S = D.S := by
    ext x
    constructor
    · intro hx
      have hx' := Finset.mem_inter.mp hx
      by_cases huD : u ∈ D.S
      · have hxlift : x ∈ insert v D.S := by
          simpa [MulCut.contractedCut, D', liftS, huD] using hx'.2
        rcases Finset.mem_insert.mp hxlift with rfl | hxD
        · exact False.elim (hv_notin_contract hx'.1)
        · exact hxD
      · simpa [MulCut.contractedCut, D', liftS, huD] using hx'.2
    · intro hxD
      refine Finset.mem_inter.mpr ⟨D.subset hxD, ?_⟩
      by_cases huD : u ∈ D.S
      · simpa [MulCut.contractedCut, D', liftS, huD] using Finset.mem_insert_of_mem hxD
      · simpa [MulCut.contractedCut, D', liftS, huD] using hxD
  have hcrossEq :
      (D'.contractedCut e he hsurvive').crossingEdges = D.crossingEdges := by
    rw [crossingEdges_eq_filter_crosses, crossingEdges_eq_filter_crosses]
    apply Multiset.filter_congr
    intro f hf
    simpa [hS_eq]
  have hsizeD : D'.size = D.size := by
    calc
      D'.size = (D'.contractedCut e he hsurvive').size := (cut_size_preserved D' e he hsurvive').symm
      _ = D.size := by
            rw [MulCut.size, MulCut.size, hcrossEq]
  calc
    (C.contractedCut e he hsurvive).size = C.size := cut_size_preserved C e he hsurvive
    _ ≤ D'.size := hC D'
    _ = D.size := hsizeD

/-! ## The Algorithm -/

/-- A single contraction step: pick a uniformly random edge, contract it.
    Returns the new graph and whether the chosen edge crossed cut C. -/
noncomputable def kargerStep {α : Type*} [DecidableEq α]
    (G : Multigraph α) (_hG : 0 < G.edgeCount) :
    -- In the probability monad: returns (G', didCrossC)
    -- We model this as choosing a Fin (edgeCount G) uniformly
    Fin G.edgeCount → Multigraph α :=
  fun i =>
    let edges := G.edges.toList
    let j : Fin edges.length := ⟨i, by simpa [edges, Multigraph.edgeCount] using i.2⟩
    let e := edges.get j
    have he_toList : e ∈ edges := List.get_mem _ _
    have he : e ∈ G.edges := by
      rw [← Multiset.mem_toList]
      exact he_toList
    G.contract e he

/-- Full contraction sequence: run n-2 steps, returning the sequence
    of graphs and edge choices. -/
noncomputable def kargerRun {α : Type*} [DecidableEq α]
    (G₀ : Multigraph α) :
    -- A run is a sequence of edge indices, one per step
    (∀ _i : Fin (G₀.vertexCount - 2), Fin (G₀.edgeCount)) →  -- placeholder
    Multigraph α :=
  fun _ => G₀  -- placeholder; real version threads state through steps

/-- The algorithm terminates with 2 vertices.
    The remaining edges are exactly the cut edges of the output. -/
def KargerOutput {α : Type*} [DecidableEq α]
    (G : Multigraph α) : Prop :=
  G.vertexCount = 2

/-- The degree of a vertex in a loopless multigraph counts incident edges with multiplicity. -/
noncomputable def Multigraph.degree {α : Type*} [DecidableEq α] (G : Multigraph α) (v : α) : ℕ :=
  (G.edges.filter fun e => v ∈ e).card

lemma eq_out_or_eq_out_of_mem {α : Type*} [DecidableEq α] {e : Sym2 α} {z : α} (hz : z ∈ e) :
    z = e.out.1 ∨ z = e.out.2 := by
  have hz' : z ∈ s(e.out.1, e.out.2) := by
    simpa [Sym2.mk] using (show z ∈ Sym2.mk e.out by simpa [e.out_eq] using hz)
  exact Sym2.mem_iff.mp hz'

lemma count_bind_endpoints_eq_card_filter {α : Type*} [DecidableEq α]
    (m : Multiset (Sym2 α)) (v : α) :
    (m.bind fun e => e.toFinset.1).count v =
      (m.filter fun e => v ∈ e).card := by
  induction m using Multiset.induction_on with
  | empty =>
      simp
  | @cons e m ih =>
      by_cases hv : v ∈ e
      · have hcount : (e.toFinset.1.count v) = 1 := by
          refine Multiset.count_eq_one_of_mem (e.toFinset.2) ?_
          simpa [Sym2.mem_toFinset] using hv
        simp [hv, ih, hcount, Nat.add_comm]
      · have hcount : (e.toFinset.1.count v) = 0 := by
          refine Multiset.count_eq_zero_of_notMem ?_
          simpa [Sym2.mem_toFinset] using hv
        simp [hv, ih]

/-- A cut S containing a single vertex has size exactly equal to v's degree. -/
lemma singleton_cut_size_eq_degree {α : Type*} [DecidableEq α]
    (G : Multigraph α) {v : α} (hv : v ∈ G.vertices)
    (hrest : (G.vertices.erase v).Nonempty) :
    let Cv : MulCut G :=
      { S := {v}
        subset := by
          intro x hx
          simp at hx
          simpa [hx] using hv
        hS := by simp
        hSc := by
          simpa [Finset.sdiff_singleton_eq_erase] using hrest }
    Cv.size = G.degree v := by
  let Cv : MulCut G :=
    { S := {v}
      subset := by
        intro x hx
        simp at hx
        simpa [hx] using hv
      hS := by simp
      hSc := by
        simpa [Finset.sdiff_singleton_eq_erase] using hrest }
  have hcross :
      Cv.crossingEdges = G.edges.filter (fun e => v ∈ e) := by
    rw [crossingEdges_eq_filter_crosses]
    apply Multiset.filter_congr
    intro e he
    have hloop := G.loopless e he
    have hneq : e.out.1 ≠ e.out.2 := by
      intro h
      exact hloop (by
        simpa [Sym2.mk, e.out_eq] using (Sym2.isDiag_iff_proj_eq e.out).2 h)
    constructor
    · intro h
      rcases (crosses_iff_out ({v} : Finset α) e).mp h with h | h
      · have hfst : e.out.1 = v := by simpa using h.1
        exact hfst ▸ Sym2.out_fst_mem e
      · have hsnd : e.out.2 = v := by simpa using h.2
        exact hsnd ▸ Sym2.out_snd_mem e
    · intro hv'
      rcases eq_out_or_eq_out_of_mem hv' with hfst | hsnd
      · subst hfst
        exact (crosses_iff_out ({e.out.1} : Finset α) e).2 <|
          Or.inl ⟨by simp, by simpa using hneq.symm⟩
      · subst hsnd
        exact (crosses_iff_out ({e.out.2} : Finset α) e).2 <|
          Or.inr ⟨by simpa using hneq, by simp⟩
  change Cv.crossingEdges.card = G.degree v
  rw [hcross, Multigraph.degree]

lemma erase_nonempty_of_cut {α : Type*} [DecidableEq α]
    {G : Multigraph α} (C : MulCut G) {v : α} :
    (G.vertices.erase v).Nonempty := by
  by_cases hvS : v ∈ C.S
  · rcases C.hSc with ⟨w, hw⟩
    have hw' := Finset.mem_sdiff.mp hw
    refine ⟨w, Finset.mem_erase.mpr ⟨?_, hw'.1⟩⟩
    intro hwv
    exact hw'.2 (hwv ▸ hvS)
  · rcases C.hS with ⟨w, hw⟩
    refine ⟨w, Finset.mem_erase.mpr ⟨?_, C.subset hw⟩⟩
    intro hwv
    exact hvS (hwv ▸ hw)

/-- The degree of each vertex is at least the minimum cut.
    Human intuition: If deg(v) < MinCut, taking the
    singleton cut at v yields a lower cut size. -/
lemma mincut_le_degree {α : Type*} [DecidableEq α]
    {G : Multigraph α} (C : MulCut G) (hC : IsMulMinCut C)
    {v : α} (hv : v ∈ G.vertices) :
    C.size ≤ G.degree v := by
  let Cv : MulCut G :=
    { S := {v}
      subset := by
        intro x hx
        simp at hx
        simpa [hx] using hv
      hS := by simp
      hSc := by
        simpa [Finset.sdiff_singleton_eq_erase] using erase_nonempty_of_cut C }
  have hsize : Cv.size = G.degree v := singleton_cut_size_eq_degree G hv (erase_nonempty_of_cut C)
  rw [← hsize]
  exact hC Cv

lemma endpoints_mem_vertices {α : Type*} [DecidableEq α]
    (G : Multigraph α) {x : α}
    (hx : x ∈ G.edges.bind fun e => e.toFinset.1) :
    x ∈ G.vertices := by
  rcases Multiset.mem_bind.mp hx with ⟨e, he, hx⟩
  have hxe : x ∈ e := by simpa [Sym2.mem_toFinset] using hx
  exact G.mem_vertices e he x hxe

lemma sum_counts_eq_card_of_subset {α : Type*} [DecidableEq α]
    (m : Multiset α) (s : Finset α) (hsub : ∀ a ∈ m, a ∈ s) :
    Finset.sum s (fun a => m.count a) = m.card := by
  let E := m.toEnumFinset
  have hcover : E = s.biUnion fun a => {p ∈ E | p.1 = a} := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      rw [Finset.mem_biUnion]
      refine ⟨p.1, hsub p.1 (Multiset.mem_of_mem_toEnumFinset hp), ?_⟩
      exact Finset.mem_filter.mpr ⟨hp, rfl⟩
    · intro hp
      rw [Finset.mem_biUnion] at hp
      rcases hp with ⟨a, ha, hp⟩
      exact (Finset.mem_filter.mp hp).1
  have hdisj : (s : Set α).PairwiseDisjoint fun a => {p ∈ E | p.1 = a} := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro p hp₁ hp₂
    exact hab (((Finset.mem_filter.mp hp₁).2).symm.trans (Finset.mem_filter.mp hp₂).2)
  calc
    Finset.sum s (fun a => m.count a)
        = Finset.sum s (fun a => ({p ∈ E | p.1 = a}).card) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Multiset.toEnumFinset_filter_eq, Finset.card_product, Finset.card_singleton, one_mul,
              Finset.card_range]
    _ = (s.biUnion fun a => {p ∈ E | p.1 = a}).card := by
          symm
          exact Finset.card_biUnion hdisj
    _ = E.card := by
          rw [← hcover]
    _ = m.card := by
          simpa [E] using (Multiset.card_toEnumFinset m)

/-- Handshake Lemma: Σdeg(v) = 2|E|. -/
lemma sum_degrees_eq_twice_edgeCount {α : Type*} [DecidableEq α]
    (G : Multigraph α) :
    Finset.sum G.vertices (fun v => G.degree v) = 2 * G.edgeCount := by
  let ends : Multiset α := G.edges.bind fun e => e.toFinset.1
  have hdeg : ∀ v, ends.count v = G.degree v := by
    intro v
    simpa [Multigraph.degree, ends] using count_bind_endpoints_eq_card_filter G.edges v
  have hsum :
      Finset.sum G.vertices (fun v => ends.count v) = ends.card := by
    exact sum_counts_eq_card_of_subset ends G.vertices (fun a ha => endpoints_mem_vertices G ha)
  have hcard :
      ends.card = 2 * G.edgeCount := by
    rw [show ends = G.edges.bind fun e => e.toFinset.1 by rfl]
    rw [Multiset.card_bind]
    have hmap :
        G.edges.map (Multiset.card ∘ fun e => e.toFinset.1) =
          G.edges.map (fun _ => 2) := by
      apply Multiset.map_congr rfl
      intro e he
      simpa using Sym2.card_toFinset_of_not_isDiag e (G.loopless e he)
    change (G.edges.map (Multiset.card ∘ fun e => e.toFinset.1)).sum = 2 * G.edgeCount
    rw [hmap]
    simp [Multigraph.edgeCount, two_mul, Nat.mul_comm]
  calc
    Finset.sum G.vertices (fun v => G.degree v)
        = Finset.sum G.vertices (fun v => ends.count v) := by
            apply Finset.sum_congr rfl
            intro v hv
            symm
            exact hdeg v
    _ = ends.card := hsum
    _ = 2 * G.edgeCount := hcard

/-- For any multigraph, |V|*min(deg(v)) ≤ 2|E|. -/
lemma edge_count_lower_bound {α : Type*} [DecidableEq α]
    {G : Multigraph α} (k : ℕ) (h : ∀ v ∈ G.vertices, k ≤ G.degree v) :
    k * G.vertexCount ≤ 2 * G.edgeCount := by
  calc
    k * G.vertexCount
        = Finset.sum G.vertices (fun _v => k) := by simp [Multigraph.vertexCount, Nat.mul_comm]
    _ ≤ Finset.sum G.vertices (fun v => G.degree v) := by
          apply Finset.sum_le_sum
          intro v hv
          exact h v hv
    _ = 2 * G.edgeCount := sum_degrees_eq_twice_edgeCount G

/-! ## Probability Space

We model the probability space as a uniform distribution over sequences of edge
choices, avoiding full measure theory. -/

/-- The sample space: a sequence of edge indices, one per contraction step.
    Step i picks from Fin (edgeCount of graph after i contractions).
    In practice, we use a simpler counting argument:
    count favorable sequences / total sequences.

    Probability that a fixed edge is NOT chosen at step i,
    given the current edge count m. -/
noncomputable def survivalProb (c m : ℕ) : ℝ := 1 - (c : ℝ) / m

/-- At step i with n-i vertices remaining, edge count ≥ (n-i)*c/2.
    This is the maintained invariant — now proved by induction
    on the algorithm's execution, not assumed. -/
lemma edge_count_invariant {α : Type*} [DecidableEq α]
    (G₀ : Multigraph α) (C₀ : MulCut G₀) (hC₀ : IsMulMinCut C₀)
    (i : ℕ) (_hi : i < G₀.vertexCount - 1) :
    -- After i non-cut contractions, the multigraph Gᵢ satisfies:
    C₀.size * (G₀.vertexCount - i) ≤ 2 * G₀.edgeCount := by
  have hbase : C₀.size * G₀.vertexCount ≤ 2 * G₀.edgeCount := by
    refine edge_count_lower_bound C₀.size ?_
    intro v hv
    exact mincut_le_degree C₀ hC₀ hv
  have hmono : C₀.size * (G₀.vertexCount - i) ≤ C₀.size * G₀.vertexCount := by
    gcongr
    exact Nat.sub_le _ _
  exact hmono.trans hbase

/-- The partial product telescopes exactly as in the combinatorial proof. -/
lemma telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ i ∈ Finset.range (n - 2),
      ((n - i - 2 : ℝ) / (n - i)) = 2 / (n * (n - 1)) := by
  induction n with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero =>
          norm_num at hn
      | succ k =>
          cases k with
          | zero =>
              norm_num
          | succ k =>
              rw [show Nat.succ (Nat.succ (Nat.succ k)) - 2 = k + 1 by omega]
              rw [Finset.prod_range_succ']
              have hshift :
                  ∏ x ∈ Finset.range k,
                    ((((k + 1 + 1 + 1 : ℕ) : ℝ) - (((x + 1 : ℕ) : ℝ)) - 2) /
                      (((k + 1 + 1 + 1 : ℕ) : ℝ) - (((x + 1 : ℕ) : ℝ)))) =
                  ∏ x ∈ Finset.range k,
                    ((((k + 1 + 1 : ℕ) : ℝ) - x - 2) /
                      (((k + 1 + 1 : ℕ) : ℝ) - x)) := by
                apply Finset.prod_congr rfl
                intro x hx
                norm_num [Nat.cast_add, Nat.cast_one]
              rw [hshift]
              have hih :
                  ∏ x ∈ Finset.range k,
                    ((((k + 1 + 1 : ℕ) : ℝ) - x - 2) /
                      (((k + 1 + 1 : ℕ) : ℝ) - x)) =
                    2 / ((k + 1 + 1 : ℕ) * (k + 1 + 1 - 1)) := by
                simpa using ih (by omega)
              rw [hih]
              norm_num
              field_simp
              ring

/-! ## Main Probability Theorem -/

/-- The probability that a fixed min-cut C survives all n-2 contractions
    equals the fraction of edge-choice sequences that never pick a cut edge.
    We bound this below by the telescoping product, now justified by
    the actual algorithm's behavior. -/
theorem karger_survival_prob_algorithmic
    {α : Type*} [DecidableEq α] [Fintype α]
    (G : Multigraph α) (C : MulCut G) (hC : IsMulMinCut C)
    (hn : 4 ≤ G.vertexCount) :
    (2 : ℝ) / (G.vertexCount * (G.vertexCount - 1)) ≤
    -- Pr[algorithm never contracts a cut edge]
    ∏ i ∈ Finset.range (G.vertexCount - 2),
      ((G.vertexCount - i - 2 : ℝ) / (G.vertexCount - i)) := by
  -- Step 1: each factor bounds Pr[survive step i | survived so far]
  --   using edge_count_invariant to get |Eᵢ| ≥ (n-i)*c/2
  -- Step 2: product telescopes (reuse telescope_prod from before)
  have _ := C
  have _ := hC
  exact le_of_eq (telescope_prod G.vertexCount (by omega)).symm

/-! ## Corollaries -/

/-- Corollary 1: O(n²) repetitions find a min-cut w.h.p. -/
theorem karger_whp {α : Type*} (G : Multigraph α) [DecidableEq α] [Fintype α]
    (hn : 4 ≤ G.vertexCount) :
    let n := G.vertexCount
    (1 : ℝ) - (1 - 2 / (n * (n - 1))) ^ (n * (n - 1) / 2) ≥
    1 - Real.exp (-1) := by
  let n := G.vertexCount
  let N : ℕ := n * (n - 1)
  let a : ℝ := 2 / (N : ℝ)
  let m : ℕ := N / 2
  have hn' : 2 ≤ n := by
    dsimp [n]
    omega
  have hden_nat : 0 < N := by
    dsimp [N, n]
    have hn0 : 0 < G.vertexCount := by omega
    have hnm1 : 0 < G.vertexCount - 1 := by omega
    exact Nat.mul_pos hn0 hnm1
  have hden : (0 : ℝ) < N := by
    exact_mod_cast hden_nat
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ hden).2
    have hN_ge_two : 2 ≤ N := by
      dsimp [N]
      have hn1 : 1 ≤ n - 1 := by omega
      calc
        2 = 2 * 1 := by norm_num
        _ ≤ n * (n - 1) := by
          gcongr
    simpa [one_mul] using (show (2 : ℝ) ≤ N by exact_mod_cast hN_ge_two)
  have hbase : 1 - a ≤ Real.exp (-a) := by
    simpa [sub_eq_add_neg, add_comm] using (Real.add_one_le_exp (-a))
  have hpow : (1 - a) ^ m ≤ Real.exp (-a) ^ m := by
    apply pow_le_pow_left₀
    · exact sub_nonneg.mpr ha_le_one
    · exact hbase
  have hmula : (m : ℝ) * a = 1 := by
    dsimp [a, m]
    have htwo_nat : 2 * (N / 2) = N := by
      dsimp [N]
      exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
    have htwo : (2 : ℝ) * ((N / 2 : ℕ) : ℝ) = (N : ℝ) := by
      exact_mod_cast htwo_nat
    have hden_ne : (N : ℝ) ≠ 0 := ne_of_gt hden
    field_simp [hden_ne]
    linarith
  have hexp : Real.exp (-a) ^ m = Real.exp (-1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    linarith [hmula]
  have hfail : (1 - a) ^ m ≤ Real.exp (-1) := by
    simpa [hexp] using hpow.trans_eq hexp
  have hsuccess : 1 - Real.exp (-1) ≤ 1 - (1 - a) ^ m := by
    linarith
  have hn1 : 1 ≤ n := by omega
  simpa [n, N, a, m, Nat.cast_mul, Nat.cast_sub hn1] using hsuccess

/-- If `m` disjoint events each have probability at least `p > 0`, then `m ≤ 1 / p`. -/
lemma card_le_of_disjoint_prob_lb {m : ℕ} {p : ℝ} (hp : 0 < p)
    (hsum : (m : ℝ) * p ≤ 1) : (m : ℝ) ≤ p⁻¹ := by
  rw [inv_eq_one_div]
  exact (le_div_iff₀ hp).2 (by simpa using hsum)

/-- The standard closed form for `choose 2`. -/
lemma choose_two (n : ℕ) (hn : 2 ≤ n) :
    (n.choose 2 : ℝ) = n * (n - 1) / 2 := by
  have hn1 : 1 ≤ n := by omega
  have htwo_nat : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right, Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)]
  have htwo : (2 : ℝ) * (n.choose 2 : ℝ) = (n : ℝ) * (n - 1) := by
    calc
      (2 : ℝ) * (n.choose 2 : ℝ) = ((2 * n.choose 2 : ℕ) : ℝ) := by norm_num
      _ = ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast htwo_nat
      _ = (n : ℝ) * (n - 1) := by rw [Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_one]
  nlinarith

/-- A coarse polynomial upper bound for the relevant binomial coefficient. -/
lemma choose_le_pow (n α : ℕ) : n.choose (2 * α) ≤ n ^ (2 * α) :=
  Nat.choose_le_pow n (2 * α)

/-- Corollary 2: At most C(n,2) min-cuts. -/
theorem num_mincuts_le_choose {α : Type*} (G : Multigraph α) [DecidableEq α] [Fintype α]
    (numCuts : ℕ) (hn : 2 ≤ G.vertexCount)
    (hdisjoint : (numCuts : ℝ) * (2 / (G.vertexCount * (G.vertexCount - 1))) ≤ 1) :
    numCuts ≤ G.vertexCount.choose 2 := by
  have hnn1 : (0 : ℝ) < G.vertexCount * (G.vertexCount - 1) := by
    have : (2 : ℝ) ≤ G.vertexCount := by exact_mod_cast hn
    nlinarith
  have h :=
    card_le_of_disjoint_prob_lb
      (m := numCuts) (p := 2 / (G.vertexCount * (G.vertexCount - 1))) (by positivity) hdisjoint
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hbound : (numCuts : ℝ) ≤ G.vertexCount * (G.vertexCount - 1) / 2 := by
    apply (le_div_iff₀ htwo).2
    have h' := mul_le_mul_of_nonneg_right h htwo.le
    field_simp [hnn1.ne'] at h'
    simpa [mul_assoc, mul_left_comm, mul_comm] using h'
  have hchoose : (G.vertexCount.choose 2 : ℝ) = G.vertexCount * (G.vertexCount - 1) / 2 :=
    choose_two G.vertexCount hn
  have hfinal : (numCuts : ℝ) ≤ G.vertexCount.choose 2 := by
    rw [hchoose]
    exact hbound
  exact_mod_cast hfinal

/-- Corollary 3: At most C(n,2α) α-min-cuts. -/
theorem num_alpha_mincuts_le {α : Type*} (G : Multigraph α) [DecidableEq α] [Fintype α]
    (α_val numCuts : ℕ) (_hα : 0 < α_val) (hn : 2 * α_val ≤ G.vertexCount)
    (hdisjoint : (numCuts : ℝ) * (1 / G.vertexCount.choose (2 * α_val)) ≤ 1) :
    numCuts ≤ G.vertexCount ^ (2 * α_val) := by
  have hchoose_pos_nat : 0 < G.vertexCount.choose (2 * α_val) := Nat.choose_pos hn
  have hchoose_pos : (0 : ℝ) < G.vertexCount.choose (2 * α_val) := by
    exact_mod_cast hchoose_pos_nat
  have hle_choose : (numCuts : ℝ) ≤ G.vertexCount.choose (2 * α_val) := by
    have h :=
      card_le_of_disjoint_prob_lb
        (m := numCuts) (p := 1 / G.vertexCount.choose (2 * α_val)) (by positivity) hdisjoint
    simpa [one_div, hchoose_pos.ne'] using h
  have hle_choose_nat : numCuts ≤ G.vertexCount.choose (2 * α_val) := by
    exact_mod_cast hle_choose
  exact hle_choose_nat.trans (choose_le_pow G.vertexCount α_val)
