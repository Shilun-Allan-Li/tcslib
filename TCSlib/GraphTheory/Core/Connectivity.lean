import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ZMod.Basic

/-!
# Bondy & Murty, *Graph Theory with Applications* — Chapter 3: Connectivity

Sorry-skeleton extracted from `papers/bondy-murty-ch3-connectivity.md`.

Now replaced by actual lean proof.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Key Definitions -/

/-- A **vertex cut**: a proper subset `S` whose deletion leaves `G` disconnected.

## Book definition (§3.1, p. 50) — verbatim

> A *vertex cut* of $G$ is a subset $V'$ of $V$ such that $G - V'$ is
> disconnected. A *$k$-vertex cut* is a vertex cut of $k$ elements. A complete
> graph has no vertex cut; in fact, the only graphs which do not have vertex
> cuts are those that contain complete graphs as spanning subgraphs.

## In Lean notation

`V'` is a `Finset V`, and "`G - V'` is disconnected" is
`¬ (G.induce (↑S)ᶜ).Connected`.  The conjunct `↑S ⊂ Set.univ` records that a
vertex cut is a *proper* subset: without it `S = V` would qualify vacuously,
since Mathlib's `Connected` is false on the empty induced graph.

A `k`-vertex cut is the pair `G.IsVertexCut S ∧ S.card = k`; that is exactly
what `vertexConnectivity` minimises over.
-/
def IsVertexCut (G : SimpleGraph V) (S : Finset V) : Prop :=
  (↑S : Set V) ⊂ Set.univ ∧ ¬ (G.induce ((↑S : Set V)ᶜ)).Connected

/-- An **edge cut**: a set of edges of `G` whose deletion leaves `G` disconnected.

## Book definition (§3.1, p. 50; recalled from §2.2) — verbatim

> Recall that an edge cut of $G$ is a subset of $E$ of the form $[S, \bar{S}]$,
> where $S$ is a nonempty proper subset of $V$. A *$k$-edge cut* is an edge cut
> of $k$ elements. If $G$ is nontrivial and $E'$ is an edge cut of $G$, then
> $G - E'$ is disconnected.

## In Lean notation

Rather than carry the book's `[S, S̄]` presentation, the definition is taken in
its *operative* form — a set of edges whose removal disconnects `G`:
`↑F ⊆ G.edgeSet ∧ ¬ (G.deleteEdges ↑F).Connected`.

The two agree on what is minimised: every `[S, S̄]` disconnects `G`, and every
disconnecting edge set contains one (take `S` a component of `G - F`).  Since
`edgeConnectivity` only ever asks for the *minimum* size, the coarser form is
equivalent for all purposes in this chapter.
-/
def IsEdgeCut (G : SimpleGraph V) (F : Finset (Sym2 V)) : Prop :=
  (↑F : Set (Sym2 V)) ⊆ G.edgeSet ∧ ¬ (G.deleteEdges (↑F : Set (Sym2 V))).Connected

open scoped Classical in
/-- Vertex connectivity `κ(G)`.  If a vertex cut exists it is the minimum cut size;
otherwise (complete graphs) it is `ν − 1`.

## Book definition (§3.1, p. 50) — verbatim

> If $G$ has at least one pair of distinct nonadjacent vertices, the
> *connectivity* $\kappa(G)$ of $G$ is the minimum $k$ for which $G$ has a
> $k$-vertex cut; otherwise, we define $\kappa(G)$ to be $\nu - 1$. Thus
> $\kappa(G) = 0$ if $G$ is either trivial or disconnected.

## In Lean notation

The book's case split is on "`G` has a pair of distinct nonadjacent vertices";
the Lean split is on the equivalent "`G` has a vertex cut at all", which is the
condition the two branches actually need.  So

* some cut exists ⇒ `κ = sInf {S.card | G.IsVertexCut S}`;
* no cut exists (the complete graphs) ⇒ `κ = ν - 1`.

`sInf` on `ℕ` is Mathlib's `Nat.sInf`, with `sInf ∅ = 0`; the `if` guard means
that fallback is never reached here.  Natural subtraction makes `ν - 1 = 0`
when `V` is empty, matching "trivial ⇒ `κ = 0`".
-/
noncomputable def vertexConnectivity (G : SimpleGraph V) : ℕ :=
  if ∃ S : Finset V, G.IsVertexCut S then
    sInf {n : ℕ | ∃ S : Finset V, G.IsVertexCut S ∧ S.card = n}
  else
    Fintype.card V - 1

/-- Edge connectivity `κ'(G)`: the minimum size of an edge cut (`sInf ∅ = 0`).

## Book definition (§3.1, p. 50) — verbatim

> we then define the *edge connectivity* $\kappa'(G)$ of $G$ to be the minimum
> $k$ for which $G$ has a $k$-edge cut. If $G$ is trivial, $\kappa'(G)$ is
> defined to be zero. Thus $\kappa'(G) = 0$ if $G$ is either trivial or
> disconnected, and $\kappa'(G) = 1$ if $G$ is a connected graph with a cut edge.

## In Lean notation

`κ' = sInf {F.card | G.IsEdgeCut F}`, with no `if` guard: the book's special
case "`G` trivial ⇒ `κ' = 0`" is already delivered by `Nat.sInf ∅ = 0`, since a
trivial graph is connected and so admits no edge cut at all.  That convention is
used directly in `edgeConnectivity_le_minDegree`.
-/
noncomputable def edgeConnectivity (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ F : Finset (Sym2 V), G.IsEdgeCut F ∧ F.card = n}

/-- `G` is `k`-connected.

## Book definition (§3.1, p. 50) — verbatim

> $G$ is said to be *$k$-connected* if $\kappa(G) \geq k$. All nontrivial
> connected graphs are 1-connected.

## In Lean notation

A literal abbreviation for `k ≤ G.vertexConnectivity`.
-/
def IsKConnected (G : SimpleGraph V) (k : ℕ) : Prop := k ≤ G.vertexConnectivity

/-- `G` is `k`-edge-connected.

## Book definition (§3.1, p. 50) — verbatim

> $G$ is said to be *$k$-edge-connected* if $\kappa'(G) \geq k$. All nontrivial
> connected graphs are 1-edge-connected.

## In Lean notation

A literal abbreviation for `k ≤ G.edgeConnectivity`.
-/
def IsKEdgeConnected (G : SimpleGraph V) (k : ℕ) : Prop := k ≤ G.edgeConnectivity

/-- `v` is a **cut vertex**: `G` is connected but deleting `v` disconnects it.

## Book definition (§2.3, p. 30; used throughout §3.2) — verbatim

> A vertex $v$ of $G$ is a *cut vertex* if $E$ can be partitioned into two
> nonempty subsets $E_1$ and $E_2$ such that $G[E_1]$ and $G[E_2]$ have just the
> vertex $v$ in common. If $G$ is loopless and nontrivial, then $v$ is a cut
> vertex of $G$ if and only if $\omega(G - v) > \omega(G)$.

## In Lean notation

A `SimpleGraph` is loopless by construction, so the second (component-counting)
characterisation is the usable one and is what is taken as the definition here.
Specialising it to a *connected* `G` — where `ω(G) = 1` — turns
`ω(G - v) > ω(G)` into "`G - v` is disconnected", giving
`G.Connected ∧ ¬ (G.induce {v}ᶜ).Connected`.

Folding `G.Connected` into the definition is what makes `IsBlock` below read as
the book's "connected graph that has no cut vertices".
-/
def IsCutVertex (G : SimpleGraph V) (v : V) : Prop :=
  G.Connected ∧ ¬ (G.induce ({v}ᶜ : Set V)).Connected

/-- A **block**: connected with no cut vertex.

## Book definition (§3.2, p. 52) — verbatim

> A connected graph that has no cut vertices is called a *block*. Every block
> with at least three vertices is 2-connected. A *block of a graph* is a
> subgraph that is a block and is maximal with respect to this property. Every
> graph is the union of its blocks.

## In Lean notation

Only the first sentence is formalised: `G.Connected ∧ ∀ v, ¬ G.IsCutVertex v`,
i.e. "`G` *is* a block".  The relative notion "a block *of* `G`" (a maximal such
subgraph) and the decomposition "every graph is the union of its blocks" are not
defined in this file — nothing in chapter 3 as formalised here needs them.

The second sentence is a theorem, proved below as
`block_three_vertices_two_connected`.
-/
def IsBlock (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ v : V, ¬ G.IsCutVertex v

/-- Two `u`–`v` walks are **internally disjoint** if they share no internal vertex.

## Book definition (§3.2, p. 52) — verbatim

> A family of paths in $G$ is said to be *internally-disjoint* if no vertex of
> $G$ is an internal vertex of more than one path of the family.

## In Lean notation

Specialised to a family of *two* `u`–`v` walks.  "`x` is an internal vertex of
`p`" is `x ∈ p.support ∧ x ≠ u ∧ x ≠ v`, so "no `x` is internal to both" becomes

    ∀ x, x ∈ p.support → x ∈ q.support → x = u ∨ x = v.

⚠ Note this does **not** forbid `p = q`.  For adjacent `u, v` the single edge
satisfies it with `p = q`, its only vertices being the two endpoints.  Theorem
3.2 as stated therefore cannot yield a cycle, which is why Corollary 3.2.1 is
derived from the edge-disjointness-carrying strengthening
`exists_two_internally_disjoint_paths_of_two_connected` rather than from
`two_connected_iff_two_internally_disjoint_paths` directly.
-/
def InternallyDisjoint {u v : V} (p q : G.Walk u v) : Prop :=
  ∀ x : V, x ∈ p.support → x ∈ q.support → x = u ∨ x = v

/-- A finite family of `u`–`v` walks, pairwise internally disjoint (family form, for Menger).

## Book context (§3.2, p. 54) — verbatim

> Theorem 3.2 has a generalisation to $k$-connected graphs, known as *Menger's
> theorem*: a graph $G$ with $\nu \geq k + 1$ is $k$-connected if and only if
> any two distinct vertices of $G$ are connected by at least $k$
> internally-disjoint paths. There is also an edge analogue of this theorem: a
> graph $G$ is $k$-edge-connected if and only if any two distinct vertices of
> $G$ are connected by at least $k$ edge-disjoint paths. Proofs of these
> theorems will be given in chapter 11.

## In Lean notation

The family form needed to *state* Menger: a `Finset` of `u`–`v` walks that is
pairwise internally disjoint.  "At least `k` paths" is then a cardinality
condition on that `Finset`.

Menger itself is deliberately **not** stated in this file — the book defers its
proof to chapter 11, so it lives in `Networks.lean` (`menger_vertex_graph`,
`menger_edge_graph`).  This definition exists so that chapter 11 can refer back
to a chapter-3 notion.
-/
def PairwiseInternallyDisjoint {u v : V} (ps : Finset (G.Walk u v)) : Prop :=
  (ps : Set (G.Walk u v)).Pairwise
    (fun p q => ∀ x, x ∈ p.support → x ∈ q.support → x = u ∨ x = v)

/-- Edge subdivision: replace `e = uv` by a length-2 path through a new vertex.

## Book definition (§3.2, p. 53) — verbatim

> It is convenient, now, to introduce the operation of subdivision of an edge.
> An edge $e$ is said to be *subdivided* when it is deleted and replaced by a
> path of length two connecting its ends, the internal vertex of this path being
> a new vertex.

## In Lean notation

Subdivision grows the vertex set by one, so unlike edge deletion it *changes the
carrier type*: `V ⊕ Unit`, with `Sum.inr ()` the new midpoint.  Adjacency:

* `inl x ~ inl y` iff `G.Adj x y` and `s(x, y) ≠ e` — the old edges, minus `e`;
* `inl x ~ inr _` iff `x ∈ e`               — the two new half-edges;
* `inr _ ~ inr _` never                     — no loop at the midpoint.

## Where it is used

Corollary 3.2.2 only, via the book's remark that *"the class of blocks with at
least three vertices is closed under the operation of subdivision"*.  That
closure property is itself unproved here, which is the main obstacle to
`block_edges_on_common_cycle`.
-/
noncomputable def subdivide (G : SimpleGraph V) (e : Sym2 V) : SimpleGraph (V ⊕ Unit) where
  Adj a b := match a, b with
    | Sum.inl x, Sum.inl y => G.Adj x y ∧ s(x, y) ≠ e
    | Sum.inl x, Sum.inr _ => x ∈ e
    | Sum.inr _, Sum.inl y => y ∈ e
    | Sum.inr _, Sum.inr _ => False
  symm := by
    rintro (x | _) (y | _) hab
    · exact ⟨hab.1.symm, by rw [Sym2.eq_swap]; exact hab.2⟩
    · exact hab
    · exact hab
    · exact hab
  loopless := by
    rintro (x | _) hx
    · exact G.loopless x hx.1
    · exact hx

/-! ## Theorem 3.1 (Whitney): κ ≤ κ' ≤ δ -/

/-- **Theorem 3.1**, second inequality: `κ' ≤ δ`.

## Book statement (§3.1, p. 51) — verbatim

> **Theorem 3.1** $\kappa \leq \kappa' \leq \delta$.

## Book proof (§3.1, p. 51) — verbatim

> If $G$ is trivial, then $\kappa' = 0 \leq \delta$. Otherwise, the set of links
> incident with a vertex of degree $\delta$ constitute a $\delta$-edge cut of
> $G$. It follows that $\kappa' \leq \delta$.

## In Lean notation

If `G` is trivial then `κ' = 0 ≤ δ`.  Otherwise take `v` with `d(v) = δ`; the
`δ` edges incident with `v` form an edge cut, since deleting them isolates `v`.
Hence `κ' ≤ d(v) = δ`.

## Proof plan

0. Split on `Subsingleton V` vs `Nontrivial V` — the book's "trivial" case.
   Trivial: every graph on a subsingleton is `Connected`, so no `F` is an edge
   cut, the set being minimised is empty, and `sInf ∅ = 0 ≤ δ`.
1. Otherwise pick `v` with `δ = d(v)` (`exists_minimal_degree_vertex`) and some
   `w ≠ v` (`exists_ne`, which is where `Nontrivial` is used).
2. Exhibit the cut `F := G.incidenceFinset v`, of size `d(v)`
   (`card_incidenceFinset_eq_degree`):
   * `↑F ⊆ G.edgeSet` by `incidenceSet_subset`;
   * `G - F` is disconnected — deleting every edge at `v` isolates `v`, so no
     walk reaches `w`.  Case on the walk: `nil` forces `w = v`; `cons` produces
     an edge at `v` that was deleted (`mk'_mem_incidenceSet_left_iff`).
3. `Nat.sInf_le` on that membership gives `κ' ≤ d(v) = δ`.

## Book remark (§3.1, p. 51) — verbatim

> The inequalities in theorem 3.1 are often strict. For example, the graph $G$
> of figure 3.2 has $\kappa = 2$, $\kappa' = 3$ and $\delta = 4$.
-/
theorem edgeConnectivity_le_minDegree [Nonempty V] :
    G.edgeConnectivity ≤ G.minDegree := by
  classical
  rcases subsingleton_or_nontrivial V with hsub | hnt
  · -- Step 0: the trivial graph has no edge cut at all, so `κ' = sInf ∅ = 0`.
    have hempty : {n : ℕ | ∃ F : Finset (Sym2 V), G.IsEdgeCut F ∧ F.card = n} = ∅ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      rintro F ⟨⟨-, hdisc⟩, -⟩
      refine hdisc ⟨fun a b => ?_⟩
      obtain rfl : a = b := Subsingleton.elim a b
      exact Reachable.refl a
    have : G.edgeConnectivity = 0 := by
      show sInf {n : ℕ | ∃ F : Finset (Sym2 V), G.IsEdgeCut F ∧ F.card = n} = 0
      rw [hempty]; exact Nat.sInf_empty
    omega
  · -- Steps 1–3.
    obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
    obtain ⟨w, hw⟩ := exists_ne v
    rw [hv]
    refine Nat.sInf_le ⟨G.incidenceFinset v, ⟨?_, ?_⟩, G.card_incidenceFinset_eq_degree v⟩
    · -- (a) the incidence set consists of edges
      simpa [SimpleGraph.incidenceFinset] using G.incidenceSet_subset v
    · -- (b) deleting every edge at `v` isolates `v`, so `w` is unreachable from `v`
      intro hconn
      obtain ⟨p⟩ := hconn.preconnected v w
      cases p with
      | nil => exact hw rfl
      | cons hadj _ =>
          rw [SimpleGraph.deleteEdges_adj] at hadj
          exact hadj.2 (by
            simpa [SimpleGraph.incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_left_iff]
              using hadj.1)

/-- Helper for Theorem 3.1: `κ ≤ ν - 1` always.

## Book context (§3.1, p. 51)

No separate statement in the book — this is the bound the proof of Theorem 3.1
invokes inline, in the branch

> either $\nu(G - S) = 2$ and
> $$\kappa(G) \leq \nu(G) - 1 = \kappa(H) + 1 \leq k$$

## In Lean notation

A vertex cut is by definition a *proper* subset of `V`, so it omits some vertex
and therefore has at most `ν - 1` elements; and in the no-vertex-cut case `κ` is
*defined* to be `ν - 1`.  Either way `κ ≤ ν - 1`.

## Proof plan

1. `unfold vertexConnectivity` and `split_ifs`.
2. Cut branch: `Nat.sInf_mem` realises `κ` as an actual cut `S`; `S ⊂ univ`
   gives some `x ∉ S`, so `Finset.card_lt_univ_of_notMem` bounds `S.card`.
3. No-cut branch: `κ = ν - 1` definitionally, so `le_rfl`.
-/
theorem vertexConnectivity_le_card_pred :
    G.vertexConnectivity ≤ Fintype.card V - 1 := by
  classical
  unfold vertexConnectivity
  split_ifs with hcut
  · -- `κ` is realised by an actual cut `S`, which omits some vertex.
    have hne : {n : ℕ | ∃ S : Finset V, G.IsVertexCut S ∧ S.card = n}.Nonempty := by
      obtain ⟨S, hS⟩ := hcut
      exact ⟨S.card, S, hS, rfl⟩
    obtain ⟨S, hS, hcard⟩ := Nat.sInf_mem hne
    rw [← hcard]
    obtain ⟨x, -, hx⟩ := Set.exists_of_ssubset hS.1
    have hxS : x ∉ S := by simpa using hx
    have := Finset.card_lt_univ_of_notMem hxS
    omega
  · exact le_rfl

/-- Core of the block criterion: a connected graph on at least three vertices
with no cut vertex has `κ ≥ 2`.

## Book context (§3.2, p. 52)

The book asserts this in passing, as the sentence that licenses applying Theorem
3.2 to blocks:

> A connected graph that has no cut vertices is called a *block*. Every block
> with at least three vertices is 2-connected.

Factored out here because *two* results need it: Theorem 3.2 (⇐), which must
turn "no 1-vertex cut" into `κ ≥ 2`, and the §3.2 remark itself
(`block_three_vertices_two_connected`).

## In Lean notation

A minimum vertex cut cannot have size `0` — that would make `G` disconnected,
contradicting `hconn` — nor size `1`, since that would exhibit a cut vertex,
contradicting `hnocut`.  And if no vertex cut exists at all then
`κ = ν - 1 ≥ 3 - 1 = 2`.

## Proof plan

1. `unfold vertexConnectivity` and `split_ifs`.
2. Cut branch: `Nat.sInf_mem` gives a realising cut `S`; `by_contra` reduces to
   `S.card = 0 ∨ S.card = 1`.
   * `S = ∅`: then `(↑S)ᶜ = univ`, and `induceUnivIso` transports `hconn` to
     contradict `hS.2`.
   * `S = {v}`: then `hS.2` is literally `¬ (G.induce {v}ᶜ).Connected`, so
     `⟨hconn, hS.2⟩ : G.IsCutVertex v` contradicts `hnocut v`.
3. No-cut branch: `κ = ν - 1 ≥ 2` by `omega` from `h : 3 ≤ ν`.
-/
theorem two_le_vertexConnectivity_of_no_cutVertex
    (hconn : G.Connected) (hnocut : ∀ v : V, ¬ G.IsCutVertex v)
    (h : 3 ≤ Fintype.card V) :
    2 ≤ G.vertexConnectivity := by
  classical
  unfold vertexConnectivity
  split_ifs with hcut
  · have hne : {n : ℕ | ∃ S : Finset V, G.IsVertexCut S ∧ S.card = n}.Nonempty := by
      obtain ⟨S, hS⟩ := hcut
      exact ⟨S.card, S, hS, rfl⟩
    obtain ⟨S, hS, hcard⟩ := Nat.sInf_mem hne
    rw [← hcard]
    by_contra hlt
    push_neg at hlt
    have : S.card = 0 ∨ S.card = 1 := by omega
    rcases this with h0 | h1
    · rw [Finset.card_eq_zero] at h0
      subst h0
      refine hS.2 ?_
      have hcoe : ((↑(∅ : Finset V) : Set V))ᶜ = Set.univ := by simp
      rw [hcoe]
      exact (induceUnivIso G).connected_iff.mpr hconn
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
      have h2 := hS.2
      rw [Finset.coe_singleton] at h2
      exact hnocut v ⟨hconn, h2⟩
  · omega

/-- Base case of Theorem 3.1's induction: `κ' = 0` forces `κ = 0`.

## Book proof (§3.1, p. 51) — verbatim

> The result is true if $\kappa' = 0$, since then $G$ must be either trivial or
> disconnected.

## In Lean notation

The book's one-liner has to be unwound through `Nat.sInf_eq_zero`, which splits
`κ' = 0` into two cases rather than one:

* `0` is attained — `∅` is an edge cut, i.e. `G` is disconnected outright; or
* the set being minimised is *empty* — no edge cut exists at all, which forces
  `V` to be a subsingleton, since otherwise deleting every edge leaves `⊥`,
  and `⊥` on a nontrivial `V` is disconnected.

These are exactly the book's "disconnected" and "trivial".  Disconnected gives
`∅` as a *vertex* cut, so `κ = 0`; subsingleton gives `κ = ν - 1 = 0`.

## Proof plan

1. `Nat.sInf_eq_zero.mp h` ⇒ `¬ G.Connected ∨ ν ≤ 1`.
   * attained case: the witnessing `F` has `card = 0`, so `F = ∅` and `hdisc`
     is `¬ G.Connected`;
   * empty case: `by_contra` gives `Nontrivial V`; then `G.edgeFinset` *is* an
     edge cut (`deleteEdges` of everything is `⊥`, disconnected by
     `connected_bot_iff`), contradicting emptiness.
2. `unfold vertexConnectivity` and discharge each case:
   * `V` empty ⇒ no cut exists (a cut omits a vertex), so `κ = ν - 1 = 0`;
   * `G` disconnected, `V` nonempty ⇒ `∅` is a vertex cut of size `0`, so
     `Nat.sInf_le` pins `κ = 0`;
   * `V` subsingleton ⇒ no cut exists, so `κ = ν - 1 = 0`.
-/
theorem vertexConnectivity_eq_zero_of_edgeConnectivity_eq_zero
    (G' : SimpleGraph V) (h : G'.edgeConnectivity = 0) :
    G'.vertexConnectivity = 0 := by
  classical
  haveI : DecidableRel G'.Adj := Classical.decRel _
  -- Step 1: `κ' = 0` means `G'` is disconnected, or `V` is a subsingleton.
  have main : ¬ G'.Connected ∨ Fintype.card V ≤ 1 := by
    rcases Nat.sInf_eq_zero.mp h with h0 | hempty
    · -- `∅` is an edge cut, i.e. `G'` itself is disconnected
      obtain ⟨F, ⟨-, hdisc⟩, hFcard⟩ := h0
      rw [Finset.card_eq_zero] at hFcard
      subst hFcard
      exact Or.inl (by simpa using hdisc)
    · -- no edge cut at all: deleting *every* edge would be one unless `V` is small
      right
      by_contra hlt
      push_neg at hlt
      haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hlt
      have hmem : G'.edgeFinset.card ∈
          {n : ℕ | ∃ F : Finset (Sym2 V), G'.IsEdgeCut F ∧ F.card = n} := by
        refine ⟨G'.edgeFinset, ⟨by simp, ?_⟩, rfl⟩
        have hbot : G'.deleteEdges (↑G'.edgeFinset) = ⊥ := by ext a b; simp
        rw [hbot, connected_bot_iff]
        rintro ⟨hsub, -⟩
        exact (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial V›) hsub
      rw [hempty] at hmem
      exact hmem
  -- Step 2: read off `κ = 0` in each case.
  unfold vertexConnectivity
  rcases main with hdisc | hsmall
  · rcases isEmpty_or_nonempty V with hE | hne
    · -- `V` empty: nothing can be a vertex cut, and `ν - 1 = 0`
      have hnocut : ¬ ∃ S : Finset V, G'.IsVertexCut S := by
        rintro ⟨S, hS⟩
        obtain ⟨x, -, -⟩ := Set.exists_of_ssubset hS.1
        exact IsEmpty.false x
      rw [if_neg hnocut]
      simp
    · -- `G'` disconnected on a nonempty `V`: `∅` is a vertex cut of size `0`
      haveI := hne
      have hcutE : G'.IsVertexCut (∅ : Finset V) := by
        refine ⟨?_, ?_⟩
        · rw [Finset.coe_empty]
          exact Set.ssubset_univ_iff.mpr Set.empty_ne_univ
        · rw [show ((↑(∅ : Finset V) : Set V))ᶜ = Set.univ by simp]
          exact fun hc => hdisc ((induceUnivIso G').connected_iff.mp hc)
      rw [if_pos ⟨∅, hcutE⟩]
      exact Nat.le_zero.mp (Nat.sInf_le ⟨∅, hcutE, Finset.card_empty⟩)
  · -- `V` a subsingleton: no vertex cut exists, and `ν - 1 = 0`
    have hnocut : ¬ ∃ S : Finset V, G'.IsVertexCut S := by
      rintro ⟨S, hS⟩
      obtain ⟨x, -, hx⟩ := Set.exists_of_ssubset hS.1
      have hxS : x ∉ S := by simpa using hx
      have hcard : S.card = 0 := by
        have := Finset.card_lt_univ_of_notMem hxS
        omega
      obtain rfl := Finset.card_eq_zero.mp hcard
      refine hS.2 ?_
      rw [show ((↑(∅ : Finset V) : Set V))ᶜ = Set.univ by simp]
      haveI : Nonempty V := ⟨x⟩
      haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hsmall
      refine (induceUnivIso G').connected_iff.mpr ⟨fun a b => ?_⟩
      obtain rfl : a = b := Subsingleton.elim a b
      exact Reachable.refl a
    rw [if_neg hnocut]
    omega

/-- Successor step, part 1: from a minimum edge cut of size `k + 1`, deleting one
of its edges drops the edge connectivity to exactly `k`.

## Book proof (§3.1, p. 51) — verbatim

> let $e$ be an edge in a $k$-edge cut of $G$. Setting $H = G - e$, we have
> $\kappa'(H) = k - 1$

## In Lean notation

Indices are shifted by one to stay in `ℕ`: the book's `κ'(G) = k` with
`κ'(H) = k - 1` is stated here as `κ'(G) = k + 1` with `κ'(G - e) = k`, which
avoids truncated subtraction entirely.

Take `F` realising `κ'(G) = k + 1`; it is nonempty, so pick `e ∈ F`.  Then
`F \ {e}` is an edge cut of `G - e` of size `k`, giving `κ'(G - e) ≤ k`; and
`κ'(G - e) ≥ k`, because a smaller cut of `G - e` together with `e` would be a
cut of `G` of size `< k + 1`, contradicting minimality.

## Proof plan

1. The set being minimised is nonempty (else `κ' = 0 ≠ k + 1`), so `Nat.sInf_mem`
   yields `F` with `F.card = k + 1`; `Finset.card_pos` gives `e ∈ F`.
2. (≤) `F.erase e` is an edge cut of `G - e`: rewrite
   `(G - e).deleteEdges ↑(F.erase e) = G.deleteEdges ↑F` via
   `deleteEdges_deleteEdges`, then reuse `hF.2`.  `Nat.sInf_le` gives `≤ k`.
3. (≥) Conversely `insert e F'` is an edge cut of `G` whenever `F'` is one of
   `G - e`, so `κ'(G) ≤ F'.card + 1`; with `κ'(G) = k + 1` and
   `Finset.card_insert_le`, `omega` closes it.
-/
theorem exists_deleteEdge_edgeConnectivity_eq
    (G' : SimpleGraph V) (k : ℕ) (h : G'.edgeConnectivity = k + 1) :
    ∃ e ∈ G'.edgeSet, (G'.deleteEdges {e}).edgeConnectivity = k := by
  classical
  -- The set whose infimum is `κ'(G')` is nonempty, else `κ' = 0 ≠ k + 1`.
  have hSne : {n : ℕ | ∃ F : Finset (Sym2 V), G'.IsEdgeCut F ∧ F.card = n}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : G'.edgeConnectivity = 0 := by
      show sInf {n : ℕ | ∃ F : Finset (Sym2 V), G'.IsEdgeCut F ∧ F.card = n} = 0
      rw [hemp]; exact Nat.sInf_empty
    omega
  obtain ⟨F, hF, hFcard⟩ := Nat.sInf_mem hSne
  have hFk : F.card = k + 1 := by rw [hFcard]; exact h
  -- `F` is nonempty, so it contains an edge `e`, which lies in `G'`.
  have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e, heF⟩ := hFne
  refine ⟨e, hF.1 (by simpa using heF), le_antisymm ?_ ?_⟩
  · -- (≤)  `F.erase e` is an edge cut of `G' - e`, of size `k`
    have hsplit : (G'.deleteEdges {e}).deleteEdges (↑(F.erase e)) = G'.deleteEdges ↑F := by
      rw [SimpleGraph.deleteEdges_deleteEdges]
      congr 1
      ext a
      simp only [Set.mem_union, Set.mem_singleton_iff, Finset.coe_erase, Set.mem_diff,
        Finset.mem_coe]
      constructor
      · rintro (rfl | ⟨ha, -⟩) <;> simp_all
      · intro ha
        by_cases hae : a = e
        · exact Or.inl hae
        · exact Or.inr ⟨ha, hae⟩
    have hcut : (G'.deleteEdges {e}).IsEdgeCut (F.erase e) := by
      refine ⟨?_, ?_⟩
      · intro a ha
        simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at ha
        simp only [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]
        exact ⟨hF.1 (by simpa using ha.1), ha.2⟩
      · rw [hsplit]; exact hF.2
    calc (G'.deleteEdges {e}).edgeConnectivity ≤ (F.erase e).card :=
          Nat.sInf_le ⟨F.erase e, hcut, rfl⟩
      _ = k := by rw [Finset.card_erase_of_mem heF, hFk]; omega

  · -- (≥)  a cut of `G' - e` together with `e` is a cut of `G'`, so `k + 1 ≤ κ'(G' - e) + 1`
    have hS'ne : {n : ℕ | ∃ F' : Finset (Sym2 V),
        (G'.deleteEdges {e}).IsEdgeCut F' ∧ F'.card = n}.Nonempty := by
      refine ⟨(F.erase e).card, F.erase e, ⟨?_, ?_⟩, rfl⟩
      · intro a ha
        simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at ha
        simp only [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]
        exact ⟨hF.1 (by simpa using ha.1), ha.2⟩
      · rw [show (G'.deleteEdges {e}).deleteEdges (↑(F.erase e)) = G'.deleteEdges ↑F by
              rw [SimpleGraph.deleteEdges_deleteEdges]
              congr 1
              ext a
              simp only [Set.mem_union, Set.mem_singleton_iff, Finset.coe_erase, Set.mem_diff,
                Finset.mem_coe]
              constructor
              · rintro (rfl | ⟨ha, -⟩) <;> simp_all
              · intro ha
                by_cases hae : a = e
                · exact Or.inl hae
                · exact Or.inr ⟨ha, hae⟩]
        exact hF.2
    obtain ⟨F', hF', hF'card⟩ := Nat.sInf_mem hS'ne
    have hins : G'.IsEdgeCut (insert e F') := by
      refine ⟨?_, ?_⟩
      · intro a ha
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha
        rcases ha with rfl | ha
        · exact hF.1 (by simpa using heF)
        · have hmem := hF'.1 (by simpa using ha)
          rw [SimpleGraph.edgeSet_deleteEdges] at hmem
          exact hmem.1
      · rw [show G'.deleteEdges (↑(insert e F')) =
              (G'.deleteEdges {e}).deleteEdges (↑F') by
              rw [SimpleGraph.deleteEdges_deleteEdges]
              congr 1
              ext a
              simp]
        exact hF'.2
    have h1 : G'.edgeConnectivity ≤ (insert e F').card := Nat.sInf_le ⟨_, hins, rfl⟩
    have h2 : (insert e F').card ≤ F'.card + 1 := Finset.card_insert_le _ _
    have h3 : F'.card = (G'.deleteEdges {e}).edgeConnectivity := hF'card
    omega

/-- Successor step, part 2: deleting a single edge drops `κ` by at most one.

## Book proof (§3.1, p. 51) — verbatim

> If $H$ contains a complete graph as a spanning subgraph, then so does $G$ and
> $$\kappa(G) = \kappa(H) \leq k - 1$$
> Otherwise, let $S$ be a vertex cut of $H$ with $\kappa(H)$ elements. Since
> $H - S$ is disconnected, either $G - S$ is disconnected, and then
> $$\kappa(G) \leq \kappa(H) \leq k - 1$$
> or else $G - S$ is connected and $e$ is a cut edge of $G - S$. In this latter
> case, either $\nu(G - S) = 2$ and
> $$\kappa(G) \leq \nu(G) - 1 = \kappa(H) + 1 \leq k$$
> or (exercise 2.3.1$a$) $G - S$ has a 1-vertex cut $\{v\}$, implying that
> $S \cup \{v\}$ is a vertex cut of $G$ and
> $$\kappa(G) \leq \kappa(H) + 1 \leq k$$

## In Lean notation

This is the heart of the induction, isolated as a standalone inequality
`κ(G) ≤ κ(G - e) + 1` so that `vertexConnectivity_le_edgeConnectivity` becomes a
three-line `calc`.  Writing `H = G - e`, the book's case analysis is:

* `H` has a complete spanning subgraph ⇒ so does `G`, and `κ(G) = κ(H)`;
* otherwise take `S` a vertex cut of `H` with `|S| = κ(H)`, and split:
  * `G - S` already disconnected ⇒ `S` is a vertex cut of `G`, so `κ(G) ≤ |S|`;
  * `G - S` connected ⇒ `e` is a cut edge (bridge) of `G - S`, and then
    * `ν(G - S) = 2` ⇒ `κ(G) ≤ ν(G) - 1 = |S| + 1`, by
      `vertexConnectivity_le_card_pred`;
    * `ν(G - S) ≥ 3` ⇒ by Exercise 2.3.1(a) `G - S` has a cut vertex `w`, and
      `S ∪ {w}` is a vertex cut of `G`, so `κ(G) ≤ |S| + 1`.

Every branch lands at `κ(G) ≤ κ(H) + 1`, which is the statement.

## Proof plan

1. Split on whether `H` admits a vertex cut at all (the Lean stand-in for the
   book's "contains a complete graph as a spanning subgraph").
2. If not, `κ(H) = ν - 1`, and `vertexConnectivity_le_card_pred` already gives
   `κ(G) ≤ ν - 1 = κ(H) ≤ κ(H) + 1`.
3. If so, `Nat.sInf_mem` realises `κ(H)` by a cut `S`, then run the three-way
   split above.  The bridge ⇒ cut-vertex step is
   `exists_isVertexCut_singleton_of_isBridge` below; combining a cut `{w}` of
   `G - S` with `S` needs `S ∪ {w}` to be shown a vertex cut of `G`, i.e. that
   `(G - S) - w = G - (S ∪ {w})` up to the induced-subgraph coercion.

## Status

`sorry`.  Step 3 is the substantial one; steps 1–2 are routine.
-/
theorem vertexConnectivity_le_deleteEdge_succ
    (G' : SimpleGraph V) (e : Sym2 V) :
    G'.vertexConnectivity ≤ (G'.deleteEdges {e}).vertexConnectivity + 1 := by
  sorry

/-- **Exercise 2.3.1(a)**, used by `vertexConnectivity_le_deleteEdge_succ`.

## Book statement (§2.3, p. 31) — verbatim

> **2.3.1** Let $G$ be connected with $\nu\ge 3$. Show that
> - (a) if $G$ has a cut edge, then $G$ has a vertex $v$ such that
>   $\omega(G-v)>\omega(G)$;
> - (b) the converse of (a) is not necessarily true.

## In Lean notation

Only part (a) is needed.  Since `G` is connected, `ω(G) = 1`, so the conclusion
`ω(G - v) > ω(G)` is "`G - v` is disconnected" — i.e. `∃ w, G.IsVertexCut {w}`.

The book leaves this as an exercise, so there is no book proof to quote; the
argument below is the standard one.

## Proof plan

1. Let `s(u, v)` be the bridge.  `isBridge_iff` says `u` and `v` lie in
   different components of `G - s(u, v)`.
2. With `ν ≥ 3` there is a third vertex `x ∉ {u, v}`.  By connectivity `x` is
   reachable from `u`; that walk avoids one of `u`, `v`.
3. Whichever of `u`, `v` lies in the component of `G - e` containing `x` is a
   cut vertex: deleting it separates the *other* endpoint from `x`, because any
   surviving path would have to use the bridge `e`, whose far end is now gone.

## Status

`sorry`.
-/
theorem exists_isVertexCut_singleton_of_isBridge
    (G' : SimpleGraph V) (hconn : G'.Connected) (h3 : 3 ≤ Fintype.card V)
    {u v : V} (hbr : G'.IsBridge s(u, v)) :
    ∃ w : V, G'.IsVertexCut {w} := by
  sorry

/-- **Theorem 3.1**, first inequality: `κ ≤ κ'`.

## Book statement (§3.1, p. 51) — verbatim

> **Theorem 3.1** $\kappa \leq \kappa' \leq \delta$.

## Book proof (§3.1, p. 51) — verbatim

> We prove that $\kappa \leq \kappa'$ by induction on $\kappa'$. The result is
> true if $\kappa' = 0$, since then $G$ must be either trivial or disconnected.
> Suppose that it holds for all graphs with edge connectivity less than $k$, let
> $G$ be a graph with $\kappa'(G) = k > 0$, and let $e$ be an edge in a $k$-edge
> cut of $G$. Setting $H = G - e$, we have $\kappa'(H) = k - 1$ and so, by the
> induction hypothesis, $\kappa(H) \leq k - 1$.
>
> If $H$ contains a complete graph as a spanning subgraph, then so does $G$ and
> $$\kappa(G) = \kappa(H) \leq k - 1$$
> Otherwise, let $S$ be a vertex cut of $H$ with $\kappa(H)$ elements. Since
> $H - S$ is disconnected, either $G - S$ is disconnected, and then
> $$\kappa(G) \leq \kappa(H) \leq k - 1$$
> or else $G - S$ is connected and $e$ is a cut edge of $G - S$. In this latter
> case, either $\nu(G - S) = 2$ and
> $$\kappa(G) \leq \nu(G) - 1 = \kappa(H) + 1 \leq k$$
> or (exercise 2.3.1$a$) $G - S$ has a 1-vertex cut $\{v\}$, implying that
> $S \cup \{v\}$ is a vertex cut of $G$ and
> $$\kappa(G) \leq \kappa(H) + 1 \leq k$$
>
> Thus in each case we have $\kappa(G) \leq k = \kappa'(G)$. The result follows
> by the principle of induction.

## In Lean notation

Induction on `κ'`.  Base `κ' = 0`: `G` is trivial or disconnected, so `κ = 0`.
Step: given `κ'(G) = k + 1`, pick `e` in a minimum edge cut; then
`κ'(G - e) = k`, so `κ(G - e) ≤ k` by the induction hypothesis, and
`κ(G) ≤ κ(G - e) + 1 ≤ k + 1 = κ'(G)`.

The entire four-way case analysis of the book's second paragraph has been
factored out into `vertexConnectivity_le_deleteEdge_succ`, so what remains here
is exactly the induction skeleton.

## Proof plan

0. Generalise over the graph, so the induction hypothesis can be applied to
   `G - e`.  The vertex type `V` is unchanged by edge deletion, so ordinary
   induction on `k = κ'(G)` suffices — we only ever step from `k + 1` to `k`.
1. `k = 0`: `vertexConnectivity_eq_zero_of_edgeConnectivity_eq_zero`.
2. `k + 1`: pick `e` with `κ'(G - e) = k` via
   `exists_deleteEdge_edgeConnectivity_eq`, then chain

       κ(G) ≤ κ(G - e) + 1     (vertexConnectivity_le_deleteEdge_succ)
            ≤ κ'(G - e) + 1    (induction hypothesis at k)
            = k + 1 = κ'(G).

## Status

Proved — but rests on `vertexConnectivity_le_deleteEdge_succ`, which is still
`sorry`.
-/
theorem vertexConnectivity_le_edgeConnectivity :
    G.vertexConnectivity ≤ G.edgeConnectivity := by
  classical
  -- Step 0: generalise the statement over all graphs on `V`.
  suffices H : ∀ k : ℕ, ∀ G' : SimpleGraph V, G'.edgeConnectivity = k →
      G'.vertexConnectivity ≤ G'.edgeConnectivity from H _ G rfl
  intro k
  induction k with
  | zero =>
      -- Step 1
      intro G' hk
      rw [hk]
      exact Nat.le_zero.mpr (vertexConnectivity_eq_zero_of_edgeConnectivity_eq_zero G' hk)
  | succ k ih =>
      -- Step 2
      intro G' hk
      obtain ⟨e, -, hek⟩ := exists_deleteEdge_edgeConnectivity_eq G' k hk
      rw [hk]
      calc G'.vertexConnectivity
          ≤ (G'.deleteEdges {e}).vertexConnectivity + 1 :=
            vertexConnectivity_le_deleteEdge_succ G' e
        _ ≤ (G'.deleteEdges {e}).edgeConnectivity + 1 := by
            have := ih (G'.deleteEdges {e}) hek
            omega
        _ = k + 1 := by rw [hek]

/-- **Theorem 3.1** (Whitney).  The full chain `κ ≤ κ' ≤ δ`.

## Book statement (§3.1, p. 51) — verbatim

> **Theorem 3.1** $\kappa \leq \kappa' \leq \delta$.

## In Lean notation

The conjunction of the two halves proved just above, packaged as the book states
it.  See `vertexConnectivity_le_edgeConnectivity` for the `κ ≤ κ'` proof and
`edgeConnectivity_le_minDegree` for `κ' ≤ δ`.

## Proof plan

`⟨vertexConnectivity_le_edgeConnectivity, edgeConnectivity_le_minDegree⟩`.

## Book remarks (§3.1, p. 51 and exercise 3.1.7, p. 52) — verbatim

> The inequalities in theorem 3.1 are often strict. For example, the graph $G$
> of figure 3.2 has $\kappa = 2$, $\kappa' = 3$ and $\delta = 4$.

> 3.1.7 Show that if $l$, $m$ and $n$ are integers such that $0<l\le m\le n$,
> then there exists a simple graph $G$ with $\kappa = l$, $\kappa' = m$, and
> $\delta = n$.

So the three parameters are independent apart from this chain — exercise 3.1.7
is not formalised in this file.
-/
theorem whitney_inequalities [Nonempty V] :
    G.vertexConnectivity ≤ G.edgeConnectivity ∧ G.edgeConnectivity ≤ G.minDegree :=
  ⟨G.vertexConnectivity_le_edgeConnectivity, G.edgeConnectivity_le_minDegree⟩

/-! ## Theorem 3.2 (Whitney 1932): 2-connected ⟺ two internally-disjoint paths -/

/-- Transfer of a walk into an induced subgraph: a walk all of whose vertices lie
in `s` witnesses reachability inside `G.induce s`.

## Book context

Pure infrastructure — no book counterpart.  The book moves freely between "a
path of `G` avoiding `w`" and "a path of `G - w`"; in Lean that transfer is a
genuine induction, because `G.induce s` has a different vertex *type*.

Used by Theorem 3.2 (⇐), where a path avoiding `w` must be seen to survive in
`G - w`.

## Proof plan

Induction on the walk.  `nil` is `Reachable.refl`; `cons` re-forms the adjacency
inside `G.induce s` from the membership hypotheses and composes with the
inductive tail.
-/
theorem reachable_induce_of_support_subset {s : Set V} :
    ∀ {u v : V} (p : G.Walk u v), (∀ x ∈ p.support, x ∈ s) →
      ∀ (hu : u ∈ s) (hv : v ∈ s), (G.induce s).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  intro u v p
  induction p with
  | nil => intro _ hu _; exact Reachable.refl _
  | @cons a b c hadj q ih =>
      intro hsup ha hc
      have hb : b ∈ s := hsup b (by simp)
      refine Reachable.trans ?_ (ih (fun x hx => hsup x (by simp [hx])) hb hc)
      exact Adj.reachable (show (G.induce s).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hadj)

/-- **Theorem 3.2 (⇒)**, strengthened to carry the edge-disjointness that
Corollary 3.2.1 needs.

## Book proof (§3.2, p. 53) — verbatim, the (⇒) direction

> Conversely, let $G$ be a 2-connected graph. We shall prove, by induction on the
> distance $d(u, v)$ between $u$ and $v$, that any two vertices $u$ and $v$ are
> connected by at least two internally-disjoint paths.
>
> Suppose, first, that $d(u, v) = 1$. Then, since $G$ is 2-connected, the edge
> $uv$ is not a cut edge and therefore, by theorem 2.3, it is contained in a
> cycle. It follows that $u$ and $v$ are connected by two internally-disjoint
> paths in $G$.
>
> Now assume that the theorem holds for any two vertices at distance less than
> $k$, and let $d(u, v) = k \geq 2$. Consider a $(u, v)$-path of length $k$, and
> let $w$ be the vertex that precedes $v$ on this path. Since $d(u, w) = k - 1$,
> it follows from the induction hypothesis that there are two
> internally-disjoint $(u, w)$-paths $P$ and $Q$ in $G$. Also, since $G$ is
> 2-connected, $G - w$ is connected and so contains a $(u, v)$-path $P'$. Let $x$
> be the last vertex of $P'$ that is also in $P \cup Q$ (see figure 3.4). Since
> $u$ is in $P \cup Q$, there is such an $x$; we do not exclude the possibility
> that $x = v$.
>
> We may assume, without loss of generality, that $x$ is in $P$. Then $G$ has two
> internally-disjoint $(u, v)$-paths, one composed of the section of $P$ from $u$
> to $x$ together with the section of $P'$ from $x$ to $v$, and the other
> composed of $Q$ together with the path $wv$.

## Why the statement is strengthened

`InternallyDisjoint p q` as defined in this file does *not* forbid `p = q`: for
adjacent `u, v` the single edge satisfies it with `p = q`, since its only
vertices are the two endpoints.  So Theorem 3.2 *as stated* cannot yield a cycle,
and the book's one-line derivation of Corollary 3.2.1 does not go through.
Adding `p.edges.Disjoint q.edges` to the conclusion repairs this; the book gets
it for free because its `d(u,v) = 1` case produces a genuine *cycle*
via theorem 2.3, not merely two paths.

## Proof plan — induction on `d(u, v)`

* `d(u, v) = 1`, i.e. `u ~ v`.  Take `p` the single edge.  By Whitney (Thm 3.1)
  `κ' ≥ κ ≥ 2`, so `{uv}` is not an edge cut and `G - uv` is still connected;
  any `u`–`v` path `q` there avoids the edge `uv`.  Internal disjointness is
  free because `p.support = [u, v]`, and edge-disjointness holds by
  construction.  (This replaces the book's appeal to theorem 2.3.)
* `d(u, v) = k ≥ 2`.  Let `w` precede `v` on a shortest `u`–`v` path, so
  `d(u, w) = k - 1`; the induction hypothesis gives internally disjoint
  `P, Q : u → w`.  Since `κ ≥ 2`, `{w}` is not a vertex cut, so `G - w` is
  connected and contains a `u`–`v` path `P'`.  Let `x` be the **last** vertex of
  `P'` lying on `P ∪ Q` — obtainable as the *first* such vertex of `P'.reverse`
  via `Walk.exists_mem_support_forall_mem_support_imp_eq` (Mathlib's
  "`takeUntilSet`" substitute).  WLOG `x ∈ P`.  The two required paths are

      (P.takeUntil x) ++ (P'.dropUntil x)    and    Q ++ (w, v).

  Their internal disjointness is exactly the maximality of `x`.

## Status

`sorry`.  The `d = 1` base case is the tractable half; the inductive step needs
the `takeUntil`/`dropUntil` bookkeeping above.
-/
theorem exists_two_internally_disjoint_paths_of_two_connected
    (hk : 2 ≤ G.vertexConnectivity) (h : 3 ≤ Fintype.card V)
    {u v : V} (huv : u ≠ v) :
    ∃ p q : G.Walk u v, p.IsPath ∧ q.IsPath ∧
      G.InternallyDisjoint p q ∧ p.edges.Disjoint q.edges := by
  sorry

/-- **Theorem 3.2** (Whitney, 1932).

## Book statement (§3.2, p. 52) — verbatim

> *Theorem 3.2* A graph $G$ with $\nu \ge 3$ is 2-connected if and only if any
> two vertices of $G$ are connected by at least two internally-disjoint paths.

## Book proof (§3.2, p. 53) — verbatim, the (⇐) direction

> If any two vertices of $G$ are connected by at least two internally-disjoint
> paths then, clearly, $G$ is connected and has no 1-vertex cut. Hence $G$ is
> 2-connected.

The (⇒) direction is quoted in full on
`exists_two_internally_disjoint_paths_of_two_connected` above, which is where it
is proved.

## In Lean notation

(⇒) is discharged by forgetting the extra edge-disjointness conjunct supplied by
the strengthened form.

(⇐) unpacks the book's "clearly".  Two steps:
* `G` is connected — the hypothesis hands back a path between any two distinct
  vertices, and `Reachable.refl` covers `a = b`;
* `G` has no cut vertex — if `w` were one, `G - w` would be disconnected, giving
  `a, b` unreachable in `G - w`.  Both supplied paths `p, q` must then pass
  through `w` (else `reachable_induce_of_support_subset` would transport them
  into `G - w`).  So `w` is a common internal vertex of `p` and `q`, and
  `InternallyDisjoint` forces `w = a` or `w = b` — contradicting that `a, b`
  live in `{w}ᶜ`.
Then `two_le_vertexConnectivity_of_no_cutVertex` converts "no cut vertex" into
`κ ≥ 2`, which is where `ν ≥ 3` is consumed.

## Proof plan

Both directions above; the whole burden sits in the strengthened (⇒) lemma.

## Book remark (§3.2, p. 54) — verbatim

> Theorem 3.2 has a generalisation to $k$-connected graphs, known as *Menger's
> theorem* [...] Proofs of these theorems will be given in chapter 11.

## Status

Proved — but rests on `exists_two_internally_disjoint_paths_of_two_connected`,
which is still `sorry`.  The (⇐) half is complete and self-contained.
-/
theorem two_connected_iff_two_internally_disjoint_paths
    (h : 3 ≤ Fintype.card V) :
    2 ≤ G.vertexConnectivity ↔
      ∀ u v : V, u ≠ v → ∃ p q : G.Walk u v,
        p.IsPath ∧ q.IsPath ∧ G.InternallyDisjoint p q := by
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  constructor
  · -- (⇒) forget the edge-disjointness supplied by the strengthened form.
    intro hκ a b hab
    obtain ⟨p, q, hp, hq, hpq, -⟩ :=
      exists_two_internally_disjoint_paths_of_two_connected G hκ h hab
    exact ⟨p, q, hp, hq, hpq⟩
  · -- (⇐) Book: "If any two vertices of `G` are connected by at least two
    -- internally-disjoint paths then, clearly, `G` is connected and has no 1-vertex cut."
    intro hpaths
    -- `G` is connected: the hypothesis hands us a path between any two distinct vertices.
    have hconn : G.Connected := by
      refine ⟨fun a b => ?_⟩
      by_cases hab : a = b
      · subst hab; exact Reachable.refl a
      · obtain ⟨p, -, -, -, -⟩ := hpaths a b hab
        exact p.reachable
    -- and no single vertex is a cut vertex
    refine two_le_vertexConnectivity_of_no_cutVertex G hconn (fun w hcv => ?_) h
    obtain ⟨-, hdisc⟩ := hcv
    -- `{w}ᶜ` is nonempty since `ν ≥ 3`
    obtain ⟨x₀, hx₀⟩ := Fintype.exists_ne_of_one_lt_card (by omega) w
    haveI : Nonempty ({w}ᶜ : Set V) := ⟨⟨x₀, by simpa using hx₀⟩⟩
    -- so "disconnected" gives two vertices of `G - w` that are unreachable there
    have hnp : ¬ (G.induce ({w}ᶜ : Set V)).Preconnected := fun hp => hdisc ⟨hp⟩
    simp only [SimpleGraph.Preconnected, not_forall] at hnp
    obtain ⟨a, b, hab⟩ := hnp
    have hau : (a : V) ≠ w := by
      have ha := a.2
      rwa [Set.mem_compl_iff, Set.mem_singleton_iff] at ha
    have hbv : (b : V) ≠ w := by
      have hb := b.2
      rwa [Set.mem_compl_iff, Set.mem_singleton_iff] at hb
    have huv : (a : V) ≠ (b : V) := by
      intro heq
      have hEq : a = b := Subtype.coe_inj.mp heq
      subst hEq
      exact hab (Reachable.refl a)
    obtain ⟨p, q, hp, hq, hpq⟩ := hpaths a b huv
    -- each of the two paths must pass through `w`, else it would survive in `G - w`
    have key : ∀ r : G.Walk (a : V) (b : V), w ∈ r.support := by
      intro r
      by_contra hnw
      refine hab (reachable_induce_of_support_subset G r (fun y hy => ?_) a.2 b.2)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      exact hnw hy
    -- but then `w` is a common internal vertex of `p` and `q`
    rcases hpq w (key p) (key q) with hwa | hwb
    · exact hau hwa.symm
    · exact hbv hwb.symm

/-! ## Corollary 3.2.1: any two vertices of a 2-connected graph lie on a common cycle -/

/-- **Corollary 3.2.1.**

## Book statement (§3.2, p. 53) — verbatim

> *Corollary 3.2.1*  If $G$ is 2-connected, then any two vertices of $G$ lie on a
> common cycle.

## Book proof (§3.2, p. 53) — verbatim

> This follows immediately from theorem 3.2 since two vertices lie on a common
> cycle if and only if they are connected by two internally-disjoint paths.

## In Lean notation

Travel out along one path and back along the other; because the two paths meet
only at the endpoints, the round trip repeats no vertex, so it is a cycle.

⚠ The book's "immediately" does **not** transfer directly.  As noted on
`InternallyDisjoint`, this file's predicate permits `p = q`, so
`two_connected_iff_two_internally_disjoint_paths` alone would let both paths be
the same single edge and `p.append q.reverse` would not be a cycle.  The proof
must therefore go through the strengthened
`exists_two_internally_disjoint_paths_of_two_connected`, whose extra
`p.edges.Disjoint q.edges` rules that degenerate case out.

## Proof plan

1. `h : 2 ≤ κ` plus `ν ≥ 3` feed
   `exists_two_internally_disjoint_paths_of_two_connected`, giving paths `p, q`
   that are internally disjoint *and* edge-disjoint.
2. Form `c := p.append q.reverse : G.Walk u u`.
3. Show `c.IsCycle`: `Walk.IsCycle` needs the support to be nodup off the
   endpoint and the walk nonempty.  Internal disjointness gives the nodup
   condition; edge-disjointness rules out `p = q`, which is what makes `c`
   nonempty and not a "there-and-straight-back" retrace.
4. `u ∈ c.support` and `v ∈ c.support` by `Walk.mem_support_append` and the fact
   that `v` is the join point.

## Status

`sorry`.  Blocked on step 1's lemma.
-/
theorem two_connected_vertices_on_common_cycle
    (h : 2 ≤ G.vertexConnectivity) (u v : V) (huv : u ≠ v) :
    ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ u ∈ c.support ∧ v ∈ c.support := by
  sorry

/-! ## Corollary 3.2.2: in a block with ν ≥ 3, any two edges lie on a common cycle -/

/-- **Corollary 3.2.2.**

## Book statement (§3.2, p. 53) — verbatim

> **Corollary 3.2.2**  If $G$ is a block with $\nu \geq 3$, then any two edges of
> $G$ lie on a common cycle.

## Book proof (§3.2, p. 53) — verbatim

> Let $G$ be a block with $\nu \geq 3$, and let $e_1$ and $e_2$ be two edges of
> $G$. Form a new graph $G'$ by subdividing $e_1$ and $e_2$, and denote the new
> vertices by $v_1$ and $v_2$. Clearly, $G'$ is a block with at least five
> vertices, and hence is 2-connected. It follows from corollary 3.2.1 that $v_1$
> and $v_2$ lie on a common cycle of $G'$. Thus $e_1$ and $e_2$ lie on a common
> cycle of $G$ (see figure 3.6).

The proof relies on a fact stated just above it in the text:

> It can be seen that the class of blocks with at least three vertices is closed
> under the operation of subdivision.

## In Lean notation

The standard device of turning an edge into a vertex, upgrading "any two
*vertices* lie on a common cycle" to "any two *edges* do".

## Proof plan

1. Subdivide twice: `(G.subdivide e₁).subdivide e₂`, on carrier
   `(V ⊕ Unit) ⊕ Unit`.  Note `subdivide` is defined for a single edge, so the
   two new vertices are `Sum.inr ()` at two different nesting levels.
2. Prove the book's unproved closure lemma — *blocks with `ν ≥ 3` are closed
   under subdivision* — for `subdivide`.  This is the real work and has no
   counterpart in the file yet.
3. `card ((V ⊕ Unit) ⊕ Unit) = ν + 2 ≥ 5`, so Corollary 3.2.1 applies to the two
   new vertices.
4. Transport the resulting cycle back down to `G`, replacing each length-2
   detour through a new vertex by the original edge.  This is the "(see figure
   3.6)" step and needs an explicit walk-level map, since the carrier types
   differ.

## Status

`sorry`.  Blocked on Corollary 3.2.1, and additionally on steps 2 and 4, neither
of which the book proves.
-/
theorem block_edges_on_common_cycle
    (hblock : G.IsBlock) (h : 3 ≤ Fintype.card V)
    (e₁ e₂ : Sym2 V) (he₁ : e₁ ∈ G.edgeSet) (he₂ : e₂ ∈ G.edgeSet) (hne : e₁ ≠ e₂) :
    ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ e₁ ∈ c.edges ∧ e₂ ∈ c.edges := by
  sorry

/-- Every block with `ν ≥ 3` is 2-connected.

## Book statement (§3.2, p. 52) — verbatim

> Every block with at least three vertices is 2-connected.

The book states this without proof, as part of the paragraph defining "block".

## In Lean notation

A block is connected and has no cut vertex, so no single vertex forms a vertex
cut; with at least three vertices this means the smallest vertex cut has size at
least `2`, i.e. `κ(G) ≥ 2`.

`ν ≥ 3` is needed to exclude the degenerate blocks `K₁` and `K₂`, which have no
cut vertex either but whose connectivity is `0` and `1` respectively.

This is the bridge that lets Corollary 3.2.2 draw on Theorem 3.2.

## Proof plan

Immediate from `two_le_vertexConnectivity_of_no_cutVertex`, unpacking
`IsBlock` into its two fields.  The substance lives in that lemma:

* no vertex cut exists ⇒ `κ = ν - 1 ≥ 3 - 1 = 2`, pure arithmetic;
* some vertex cut exists ⇒ `Nat.sInf_mem` returns a cut `S` realising `κ`; rule
  out `|S| = 0` (`S = ∅` makes `G.induce ∅ᶜ ≅ G` disconnected, contradicting
  connectivity) and `|S| = 1` (`S = {v}` is exactly `IsCutVertex v`).

## Status

Proved.
-/
theorem block_three_vertices_two_connected
    (hb : G.IsBlock) (h : 3 ≤ Fintype.card V) :
    2 ≤ G.vertexConnectivity :=
  two_le_vertexConnectivity_of_no_cutVertex G hb.1 hb.2 h

/-! ## Theorem 3.3 (Harary 1962): the Harary graph H_{m,n} is m-connected -/

/-- The Harary graph `H_{m,n}` on vertex set `ZMod n` (a circulant).

## Book construction (§3.3, pp. 56–57) — verbatim

> We shall show that equality holds in (3.1) by constructing an $m$-connected
> graph $H_{m,n}$ on $n$ vertices that has exactly $\{mn/2\}$ edges. The
> structure of $H_{m,n}$ depends on the parities of $m$ and $n$; there are three
> cases.
>
> *Case 1*    $m$ even. Let $m = 2r$. Then $H_{2r,n}$ is constructed as follows.
> It has vertices $0, 1, \ldots, n-1$ and two vertices $i$ and $j$ are joined if
> $i - r \leq j \leq i + r$ (where addition is taken modulo $n$).
>
> *Case 2*    $m$ odd, $n$ even. Let $m = 2r + 1$. Then $H_{2r+1,n}$ is
> constructed by first drawing $H_{2r,n}$ and then adding edges joining vertex
> $i$ to vertex $i + (n/2)$ for $1 \leq i \leq n/2$.
>
> *Case 3* $m$ odd, $n$ odd. Let $m = 2r + 1$. Then $H_{2r+1,n}$ is constructed
> by first drawing $H_{2r,n}$ and then adding edges joining vertex 0 to vertices
> $(n-1)/2$ and $(n+1)/2$ and vertex $i$ to vertex $i+(n+1)/2$ for
> $1 \le i < (n-1)/2$.

## In Lean notation

Arrange `n` stations in a circle and link each to its `r` nearest neighbours on
each side, adding long-range links across the circle when `m` is odd.  The
carrier is `ZMod n`, which makes the book's "addition taken modulo `n`" literal.

The three cases are a single `if`-cascade on `m % 2` and `n % 2`; Case 1 is the
base and Cases 2–3 are `⊔` with an extra chord relation.

## Status

`sorry` — the construction is **not** yet written.  Because this is a `def`
rather than a theorem, `sorry` makes `hararyGraph` an *opaque constant with no
defining equations*, so the three results below are not merely unproved but
unprovable as they stand.  Filling this definition is a prerequisite for all of
them.
-/
def hararyGraph (m n : ℕ) : SimpleGraph (ZMod n) := sorry

/-- **Theorem 3.3** (Harary, 1962).

## Book statement (§3.3, p. 57) — verbatim

> *Theorem 3.3* (Harary, 1962)   The graph $H_{m,n}$ is $m$-connected.

## Book proof (§3.3, p. 57) — verbatim

> Consider the case $m = 2r$. We shall show that $H_{2r,n}$ has no vertex cut of
> fewer than $2r$ vertices. If possible, let $V'$ be a vertex cut with
> $|V'| < 2r$. Let $i$ and $j$ be vertices belonging to different components of
> $H_{2r,n} - V'$. Consider the two sets of vertices
> $$S = \{i, i+1, \ldots, j-1, j\}$$
> and
> $$T = \{j, j+1, \ldots, i-1, i\}$$
> where addition is taken modulo $n$. Since $|V'| < 2r$, we may assume, without
> loss of generality, that $|V' \cap S| < r$. Then there is clearly a sequence of
> distinct vertices in $S \setminus V'$ which starts with $i$, ends with $j$, and
> is such that the difference between any two consecutive terms is at most $r$.
> But such a sequence is an $(i, j)$-path in $H_{2r,n} - V'$, a contradiction.
> Hence $H_{2r,n}$ is $2r$-connected.
>
> The case $m = 2r + 1$ is left as an exercise (exercise 3.3.1).

## In Lean notation

The book proves only the even case; the odd case is exercise 3.3.1, so a full
Lean proof of the statement as given must supply it.

Note the two "clearly"/"without loss of generality" steps carry real weight in
Lean: the WLOG needs `|V' ∩ S| + |V' ∩ T| ≤ |V'| + 2 < 2r + 2`, and the
"sequence of distinct vertices ... difference at most `r`" is a greedy
construction requiring an explicit induction on the arc.

## Proof plan

1. Fill `hararyGraph` first — nothing below is provable until then.
2. Even case `m = 2r`: `by_contra` on a cut `V'` with `|V'| < 2r`; take `i, j` in
   different components; define the two arcs `S`, `T` as `Finset (ZMod n)`;
   pigeonhole to get `|V' ∩ S| < r`; then build the `(i, j)`-path greedily,
   each step of size `≤ r` being an edge by the Case 1 adjacency.
3. Odd case: exercise 3.3.1, extra chord argument.
4. Conclude `κ = m` by combining the `≥ m` above with `κ ≤ δ = m`.

## Book context (§3.3, p. 56) — verbatim

> We shall denote by $f(m, n)$ the least number of edges that an $m$-connected
> graph on $n$ vertices can have. [...] By theorems 3.1 and 1.1
> $$f(m, n) \geq \{mn/2\} \tag{3.1}$$

So the point of the theorem is optimality: `H_{m,n}` attains this bound.

## Status

`sorry`, and blocked on the `hararyGraph` definition.
-/
theorem hararyGraph_isConnectivity (m n : ℕ) [NeZero n] (hmn : m < n) :
    (hararyGraph m n).vertexConnectivity = m := by
  sorry

/-- Edge count / optimality: `H_{m,n}` has `⌈mn/2⌉` edges.

## Book statement (§3.3, p. 57) — verbatim

> It is easy to see that $\varepsilon(H_{m,n}) = \{mn/2\}$. Thus, by theorem 3.3,
> $$f(m, n) \le \{mn/2\} \tag{3.2}$$
> It now follows from (3.1) and (3.2) that
> $$f(m, n) = \{mn/2\}$$
> and that $H_{m,n}$ is an $m$-connected graph on $n$ vertices with as few edges
> as possible.
>
> We note that since, for any graph $G$, $\kappa \le \kappa'$ (theorem 3.1),
> $H_{m,n}$ is also $m$-edge-connected. Thus, denoting by $g(m, n)$ the least
> possible number of edges in an $m$-edge-connected graph on $n$ vertices, we
> have, for $1 < m < n$
> $$g(m, n) = \{mn/2\} \tag{3.3}$$

## In Lean notation

The book's `{x}` is the ceiling `⌈x⌉`, so `{mn/2}` is written as the
natural-number division `(m * n + 1) / 2`.

Only `ε(H_{m,n}) = ⌈mn/2⌉` is formalised.  The optimality conclusions
`f(m,n) = ⌈mn/2⌉` and `g(m,n) = ⌈mn/2⌉` are *not* stated in this file, since
`f` and `g` (least edge counts over all `m`-connected graphs) are not defined
here.

## Proof plan

1. Fill `hararyGraph` first.
2. `H_{m,n}` is `m`-regular when `mn` is even, and `m`-regular except for one
   vertex of degree `m + 1` when `mn` is odd.  Compute `∑ degrees` by cases on
   the three construction branches.
3. Handshaking (`sum_degrees_eq_twice_card_edges`) turns that into
   `2ε = mn` or `mn + 1`, then `omega` gives `ε = (mn + 1) / 2`.

## Status

`sorry`, and blocked on the `hararyGraph` definition.
-/
theorem hararyGraph_edgeCard (m n : ℕ) [NeZero n]
    [DecidableRel (hararyGraph m n).Adj] (hmn : m < n) :
    (hararyGraph m n).edgeFinset.card = (m * n + 1) / 2 := by
  sorry

/-! ## Selected Exercises -/

/-- **Exercise 3.1.2**: a `k`-edge-connected graph satisfies `kν ≤ 2ε`.

## Book statement (§3.1, p. 52) — verbatim

> 3.1.2 Show that if $G$ is $k$-edge-connected, then $\varepsilon \ge k\nu/2$.

An exercise, so the book gives no proof.

## In Lean notation

Stated multiplicatively as `kν ≤ 2ε` to stay in the natural numbers and avoid
division.

By Theorem 3.1, `k ≤ κ' ≤ δ`, so every vertex has degree at least `k`.  Summing
over all `ν` vertices gives `∑_v d(v) ≥ kν`, and handshaking (Theorem 1.1) says
that sum equals `2ε`.  Hence `2ε ≥ kν`.

A network that survives any `k` link failures must give every station at least
`k` links, so it cannot be sparse — this is exactly the lower bound
`f(m, n) ≥ ⌈mn/2⌉` of (3.1), which §3.3 shows the Harary graphs attain.

## Proof plan

0. `V` empty ⇒ `ν = 0` and the claim is `0 ≤ 2ε`.
1. Chain `k ≤ κ' ≤ δ ≤ d(v)` for each `v`, via `edgeConnectivity_le_minDegree`
   and `minDegree_le_degree`.
2. `kν = ∑_v k ≤ ∑_v d(v)` by `Finset.sum_le_sum`.
3. `∑_v d(v) = 2ε` by `sum_degrees_eq_twice_card_edges`.

## Status

Proved.
-/
theorem edgeCard_ge_of_kEdgeConnected (k : ℕ) (h : k ≤ G.edgeConnectivity) :
    k * Fintype.card V ≤ 2 * G.edgeFinset.card := by
  classical
  rcases isEmpty_or_nonempty V with hE | hne
  · -- Step 0: no vertices, so the left-hand side is `0`.
    simp
  · -- Step 1: every degree is at least `k`, via Whitney's `κ' ≤ δ`.
    have hk : ∀ v : V, k ≤ G.degree v := fun v =>
      h.trans (G.edgeConnectivity_le_minDegree.trans (G.minDegree_le_degree v))
    calc k * Fintype.card V
        = ∑ _v : V, k := by simp [Finset.card_univ, mul_comm]
      -- Step 2
      _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum fun v _ => hk v
      -- Step 3: handshaking
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

/-- **Exercise 3.1.3(a)**: a simple graph with `δ ≥ ν − 2` has `κ = δ`.

## Book statement (§3.1, p. 52) — verbatim

> 3.1.3 (a) Show that if $G$ is simple and $\delta \ge \nu-2$, then
> $\kappa = \delta$.
> &nbsp;&nbsp;(b) Find a simple graph $G$ with $\delta = \nu-3$ and
> $\kappa < \delta$.

An exercise, so the book gives no proof.  Part (b) is not formalised.

## In Lean notation

The hypothesis says every vertex is non-adjacent to at most one other vertex, so
the graph is complete or very nearly so.  Theorem 3.1 already gives `κ ≤ δ`, so
only `κ ≥ δ` needs proving: any set of fewer than `δ` vertices fails to
disconnect such a dense graph, because any two surviving vertices are either
adjacent outright or share a common surviving neighbour.

Part (b) shows the bound is tight — one step less density (`δ = ν - 3`) already
allows `κ < δ`.

## Proof plan

1. `κ ≤ δ` from `whitney_inequalities`.
2. For `κ ≥ δ`: let `S` be any vertex cut, and show `|S| ≥ δ`.  Take `a, b` in
   different components of `G - S`.  Each of `a, b` is non-adjacent to at most
   one vertex, so `N(a) ∪ N(b)` misses at most a bounded set; since `a` and `b`
   are in different components, `N(a) ∩ N(b) ⊆ S`, and counting gives
   `|S| ≥ δ`.
3. `le_antisymm`.

## Status

`sorry`.
-/
theorem vertexConnectivity_eq_minDegree_of_delta_ge
    (h : Fintype.card V - 2 ≤ G.minDegree) :
    G.vertexConnectivity = G.minDegree := by
  sorry

/-- **Exercise 3.1.6**: a simple 3-regular graph has `κ = κ'`.

## Book statement (§3.1, p. 52) — verbatim

> 3.1.6 Show that if $G$ is simple and 3-regular, then $\kappa = \kappa'$.

An exercise, so the book gives no proof.

## In Lean notation

Theorem 3.1 gives `κ ≤ κ' ≤ δ = 3`, so both parameters lie in `{0, 1, 2, 3}` and
only `κ' ≤ κ` needs argument.  Given a minimum vertex cut `S` of size `κ`, one
converts it into an edge cut of the same size by choosing, for each `v ∈ S`, a
single suitable incident edge — possible precisely because every vertex of a
cubic graph has just three neighbours, so the local structure around a cut
vertex is tightly constrained.

Cubic graphs are the smallest interesting regular case, and this exercise records
that for them the vertex and edge measures of reliability agree — unlike the
general situation, where figure 3.2 has `κ = 2 < κ' = 3`.

## Proof plan

1. `κ ≤ κ'` from `vertexConnectivity_le_edgeConnectivity`.
2. For `κ' ≤ κ`: realise `κ` by a minimum vertex cut `S` (`Nat.sInf_mem`).  For
   each `v ∈ S`, pick an incident edge crossing between two fixed components of
   `G - S`; 3-regularity makes that choice well defined.  The resulting edge set
   has size `≤ |S| = κ` and disconnects `G`, so `Nat.sInf_le` gives `κ' ≤ κ`.
3. `le_antisymm`.

## Status

`sorry`.
-/
theorem vertexConn_eq_edgeConn_of_threeRegular
    (h : G.IsRegularOfDegree 3) :
    G.vertexConnectivity = G.edgeConnectivity := by
  sorry

/-- **Exercise 3.2.1**: 2-edge-connected ⟺ two edge-disjoint paths between any
two vertices.

## Book statement (§3.2, p. 55) — verbatim

> **3.2.1** Show that a graph is 2-edge-connected if and only if any two vertices
> are connected by at least two edge-disjoint paths.

An exercise, so the book gives no proof.  It is the `k = 2` case of the edge form
of Menger's theorem quoted on `PairwiseInternallyDisjoint` above.

## In Lean notation

The edge analogue of Whitney's Theorem 3.2, with "internally disjoint" weakened
to "edge-disjoint" and vertex cuts replaced by edge cuts.

Edge-disjoint is genuinely weaker than internally disjoint: the two routes may
pass through common intermediate stations, as long as they never use the same
link.

## Proof plan

(⇐) If any two vertices are joined by two edge-disjoint paths, no single edge
can disconnect the graph — deleting one edge kills at most one of the two routes
— so no 1-edge cut exists and `κ' ≥ 2`.  Concretely: given a 1-element edge cut
`{e}`, pick `a, b` separated by it, take the two paths, and observe at least one
avoids `e`, contradicting separation.

(⇒) In a 2-edge-connected graph no edge is a cut edge, so by Theorem 2.3 every
edge lies on a cycle; then the same induction on `d(u, v)` used for Theorem 3.2
assembles two edge-disjoint routes.  In practice this direction should reuse
`exists_two_internally_disjoint_paths_of_two_connected`, whose conclusion
already carries `p.edges.Disjoint q.edges` — the very reason that strengthening
was introduced.

## Status

`sorry`.  The (⇐) direction is self-contained and the easier half.
-/
theorem two_edge_connected_iff_two_edge_disjoint_paths :
    2 ≤ G.edgeConnectivity ↔
      ∀ u v : V, u ≠ v → ∃ p q : G.Walk u v,
        p.IsPath ∧ q.IsPath ∧ Disjoint p.edges.toFinset q.edges.toFinset := by
  sorry

-- Menger's theorem (vertex/edge form) is stated in Ch. 3 but its proof is deferred to
-- Ch. 11, and the book's candidate signature is only a placeholder (it lacks a genuine
-- "k pairwise internally-disjoint paths" family predicate). Deferred to Networks.lean.

/-! ### Book statement of the deferred item (§3.2, Menger's theorem)

*Vertex form.*  A graph `G` with `ν ≥ k + 1` is `k`-connected if and only if any
two distinct vertices of `G` are connected by at least `k` internally-disjoint
paths.

*Edge form.*  A graph `G` is `k`-edge-connected if and only if any two distinct
vertices of `G` are connected by at least `k` edge-disjoint paths.

These generalise theorem 3.2 (the case `k = 2`) and exercise 3.2.1 respectively.
Bondy & Murty state both here but defer their proofs to chapter 11, where they
fall out of the max-flow min-cut theorem; see `Networks.lean`. -/

end SimpleGraph
