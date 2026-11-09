import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Bondy & Murty, *Graph Theory with Applications* — Chapter 2: Trees

Sorry-skeleton scaffolded from `TCSlib/GraphTheory/book copy/02_chapter-2-trees.md`.

This file contains **statements only**; every proof body is `sorry`.  It is a scaffold
for sorry-driven development (fill one stub at a time, verify with `lake build`).

Much of this chapter already lives in Mathlib's `SimpleGraph.Acyclic`
(`IsTree`, `IsAcyclic`, `IsBridge`, spanning-tree existence, …).  Where a theorem is
already proved in Mathlib we still state the book's version as a `sorry`-stub and add a
`-- Mathlib: <exact.name>` comment pointing at the existing proof.  Concepts Mathlib lacks
(number of components `ω`, cut vertex, number of spanning trees `τ`, edge contraction `G·e`,
bonds/cotrees) are defined locally.

## How each declaration is annotated

Every docstring below has a fixed shape, so the book's mathematics stays separable
from this file's formalisation choices:

1. **The book's own statement** (theorem) or **definition** (`def`), quoted verbatim
   from Bondy & Murty, LaTeX transcribed into Lean-style backticks.
2. **Book proof** — B&M's printed proof, verbatim.  Chapter 2 prints proofs for
   theorems 2.1–2.10 and their corollaries, so almost every item here has one.
3. Then, depending on the state of the declaration:
   * **Proof** — for the 7 already *proved* here: what the Lean proof does, and which
     Mathlib lemma carries it.
   * **Skeleton** — for the 7 still stubbed: an abstract numbered plan keyed to the
     Lean statement.
4. **Reading** — what the result means and how it sits in the chapter.
5. **Formalisation** — only where the Lean statement departs from the book's.

Definitions carry parts 1, 4 and 5 only.

## ⚠ Three defects

* **`contract` has a `sorry` body**, so `G · e` is an opaque graph and theorem 2.8
  (deletion–contraction) is vacuous.  It is also a *same-carrier placeholder*: a
  genuine contraction changes the vertex type.
* **`IsBond` admits `∅` when `G` is disconnected.**  `IsEdgeCutSet ∅` unfolds to
  `¬ G.Connected`, and no `B' ⊂ ∅` exists, so the minimality clause is vacuous —
  making `∅` a bond, contrary to "minimal **nonempty** edge cut".  The docstring's
  claim that nonemptiness is automatic holds only for connected `G`.
* **`cayley` is false at `n = 0`**: `Fin 0` admits no tree (`IsTree` needs
  `Nonempty`), so `τ = 0`, while `0 ^ (0-2) = 0 ^ 0 = 1`.

Per-declaration detail is in the individual docstrings.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Local definitions (concepts Mathlib does not provide) -/

/-- The number of connected components `ω(G)` of a graph.

**Book definition (§1.6, used throughout chapter 2).**  Connection is an
equivalence relation on the vertex set `V`, so `V` partitions into classes
`V₁, …, V_ω`; the induced subgraphs `G[V₁], …, G[V_ω]` are the **components** of
`G`, and `ω(G)` is their number.

**Reading.**  `G` is connected exactly when `ω(G) = 1`.  This quantity is the
workhorse of chapter 2: cut edges and cut vertices are defined precisely as the
elements whose removal makes `ω` go up.

**Formalisation.**  ⚠ Missing from Mathlib as a *number* — `ConnectedComponent` is
there, but not its cardinality.  `Nat.card` rather than `Fintype.card` so no
`DecidableEq` on components is needed; over a `Fintype` carrier the two agree. -/
noncomputable def numComponents {W : Type*} (H : SimpleGraph W) : ℕ :=
  Nat.card H.ConnectedComponent

/-- A **cut vertex** (§2.3): a vertex whose deletion increases the number of components,
`ω(G − v) > ω(G)`.  (For a loopless nontrivial connected graph this is the book's
definition; the trivial graph `K₁` has no cut vertex since deleting its only vertex
yields the empty graph with `ω = 0`.)

**Book definition (§2.3).**  *A vertex `v` of `G` is a cut vertex if `E` can be
partitioned into two nonempty subsets `E₁` and `E₂` such that `G[E₁]` and
`G[E₂]` have just the vertex `v` in common.  If `G` is loopless and nontrivial,
then `v` is a cut vertex of `G` if and only if `ω(G - v) > ω(G)`.*

**Reading.**  An articulation point — a single vertex holding the graph together, so
that deleting it splits some component into two or more pieces.

**Formalisation.**  Since `SimpleGraph` is automatically loopless, B&M's two
formulations agree and the component-counting one is the convenient one.  ⚠ Note the
convention at the trivial graph: for `K₁`, `ω(G) = 1` while `G - v` is empty with
`ω = 0`, so `1 < 0` fails and `K₁` has no cut vertex — which is what the book
intends. -/
def IsCutVertex (G : SimpleGraph V) (v : V) : Prop :=
  G.numComponents < (G.induce ({v}ᶜ : Set V)).numComponents

/-- An **edge cut set**: a set of edges whose deletion disconnects `G`.

**Book definition (§2.2).**  For subsets `S` and `S'` of `V`, `[S, S']` denotes
the set of edges with one end in `S` and the other in `S'`.  An **edge cut** of
`G` is a subset of `E` of the form `[S, S̄]`, where `S` is a nonempty proper
subset of `V` and `S̄ = V \ S`.

**Reading.**  Split the vertices into two nonempty groups and collect the edges
running between them; deleting them severs every route from one group to the other.

**Formalisation.**  B&M define an edge cut *by its shape* `[S, S̄]`; this takes the
operational characterisation — a subset of `edgeSet` whose removal leaves `G`
disconnected — which for **connected** `G` describes the same collections.  ⚠ For
disconnected `G` they diverge, and `∅` satisfies this predicate; that is the source of
the `IsBond` defect below. -/
def IsEdgeCutSet (G : SimpleGraph V) (F : Set (Sym2 V)) : Prop :=
  F ⊆ G.edgeSet ∧ ¬ (G.deleteEdges F).Connected

/-- A **bond** (§2.2): a minimal (nonempty) edge cut, i.e. a minimal set of edges whose
deletion disconnects `G`.  ⚠ Nonemptiness is **not** automatic here — see the defect
note below.

**Book definition (§2.2).**  *A minimal nonempty edge cut of `G` is called a
bond; each cut edge `e`, for instance, gives rise to a bond `{e}`.  If `G` is
connected, then a bond `B` of `G` is a minimal subset of `E` such that `G - B` is
disconnected.*

**Reading.**  An edge cut with nothing to spare — remove all of it and the graph falls
apart, but put any single edge back and it is connected again.  Exercise 2.2.8
characterises when `[S, S̄]` is a bond: exactly when both `G[S]` and `G[S̄]` are
connected.  Bonds are the notion **dual** to cycles, a duality chapter 12 develops in
full — theorem 2.6 here is the mirror of theorem 2.5.

**⚠ Defect: `∅` is a bond when `G` is disconnected.**  The docstring above claims
nonemptiness is automatic because "deleting `∅` leaves `G` connected" — but that holds
only for connected `G`.  For disconnected `G`, `IsEdgeCutSet ∅` unfolds to
`¬ G.Connected`, which is true, and there is no `B' ⊂ ∅` to test, so the minimality
clause is vacuous.  Hence `IsBond G ∅`, contradicting *minimal **nonempty** edge cut*.

*The repair:* add `B.Nonempty` as a conjunct, or carry `G.Connected` as a hypothesis
wherever `IsBond` is used (theorem 2.6 already does — its `hG` is available). -/
def IsBond (G : SimpleGraph V) (B : Set (Sym2 V)) : Prop :=
  G.IsEdgeCutSet B ∧ ∀ B' ⊂ B, (G.deleteEdges B').Connected

/-- The **number of spanning trees** `τ(G)`: the number of tree subgraphs `T ≤ G` on the
full vertex set.

**Book definition (§2.4).**  *We denote the number of spanning trees of `G` by
`τ(G)`.*

**Reading.**  ⚠ `τ(G)` counts the *distinct* spanning trees, **not** the
non-isomorphic ones.  B&M stress the difference: `K₆` has six non-isomorphic spanning
trees (figure 2.1) but `6⁴ = 1296` distinct ones.  `τ` satisfies deletion–contraction
(theorem 2.8) and, for complete graphs, Cayley's formula (theorem 2.9); the general
determinant formula is chapter 12's matrix-tree theorem.

**Formalisation.**  "Spanning" is automatic: a `T : SimpleGraph W` lives on the whole
vertex type, so `T ≤ H ∧ T.IsTree` already means a spanning tree.  ⚠ `IsTree` bundles
`Connected`, which requires `Nonempty W` — so on an empty carrier `τ = 0`.  That is
where `cayley` fails at `n = 0`. -/
noncomputable def numSpanningTrees {W : Type*} (H : SimpleGraph W) : ℕ :=
  Nat.card {T : SimpleGraph W // T ≤ H ∧ T.IsTree}

/-- **Edge contraction** `G · e` (§2.4).  Mathlib has no edge contraction for `SimpleGraph`.
NOTE: a genuine contraction identifies the ends of `e` and therefore changes the carrier
type (to `|V| − 1` vertices).  Here it is *stubbed on the same carrier* `V` as a placeholder,
purely so that the deletion–contraction recurrence (Theorem 2.8) can be typed.

**Book definition (§2.4).**  *An edge `e` of `G` is said to be contracted if it is
deleted and its ends are identified; the resulting graph is denoted `G · e`.*

**Reading.**  Think of `e = uv` as a string pulled tight until `u` and `v` merge;
everything attached to either is now attached to the merged vertex, and `e`
disappears.  For a link, `ν(G·e) = ν - 1`, `ε(G·e) = ε - 1`, `ω(G·e) = ω` — so
contracting an edge of a tree again yields a tree, which is what makes
deletion–contraction work.

**⚠ Defective on two counts.**
1. *`sorry` body.*  `G · e` is an opaque graph, so theorem 2.8 relates opaque
   quantities and asserts nothing.
2. *Wrong carrier.*  A genuine contraction has `ν - 1` vertices; this is stubbed on
   the **same** carrier `V` purely so theorem 2.8 can be typed.  Even given an honest
   body on `V`, the identity `ν(G·e) = ν - 1` could not hold.

*The repair* is to move to the quotient carrier `{x : V // x ≠ v}` with `v`'s
incidences re-pointed at `u`, exactly as chapter 10's `Digraph.contractEdge` does —
that definition is honest and complete, and can be transcribed. -/
noncomputable def contract (G : SimpleGraph V) (e : Sym2 V) : SimpleGraph V := sorry

/-! ## 2.1 Trees -/

/-! ### Book definitions, §2.1 (Trees)

*Acyclic graph.*  A graph containing no cycles.

*Tree.*  A connected acyclic graph.  Figure 2.1 of the book displays the six
trees on six vertices; observe that each has five edges, which theorem 2.2
explains.

*Forest* (exercise 2.1.7).  Another name for an acyclic graph.  Each component of
a forest is a tree, and `G` is a forest if and only if `ε = ν - ω`.

*Centre* (exercise 2.1.8).  A vertex `u` minimising `max_{v ∈ V} d(u, v)`.  A
tree has either exactly one centre or two adjacent centres. -/

-- Thm 2.1: In a tree, any two vertices are joined by a unique path.
-- Mathlib: SimpleGraph.IsTree.existsUnique_path
/-- **Theorem 2.1.**  *In a tree, any two vertices are connected by a unique
path.*

**Book proof** (B&M §2.1, verbatim).  *By contradiction.  Let `G` be a tree, and
assume that there are two distinct `(u, v)`-paths `P₁` and `P₂` in `G`.  Since
`P₁ ≠ P₂`, there is an edge `e = xy` of `P₁` that is not an edge of `P₂`.  Clearly the
graph `(P₁ ∪ P₂) - e` is connected.  It therefore contains an `(x, y)`-path `P`.  But
then `P + e` is a cycle in the acyclic graph `G`, a contradiction.*

**Proof.**  `hG.existsUnique_path u v`, Mathlib.

**Reading.**  A tree has exactly enough edges to hold the vertices together and not one
more: connectivity gives at least one route between any two vertices, acyclicity
forbids a second, since two distinct routes always enclose a cycle.  ⚠ The converse
holds for loopless graphs (exercise 2.1.1), so "unique paths between all pairs" is an
equivalent definition of a tree — that direction is not stated here. -/
theorem tree_unique_path (hG : G.IsTree) (u v : V) :
    ∃! p : G.Walk u v, p.IsPath :=
  hG.existsUnique_path u v

-- Thm 2.2: A tree has ε = ν − 1  (here `edgeFinset.card + 1 = card V`).
-- Mathlib: SimpleGraph.IsTree.card_edgeFinset
/-- **Theorem 2.2.**  *If `G` is a tree, then `ε = ν - 1`.*

**Book proof** (B&M §2.1, verbatim).  *By induction on `ν`.  When `ν = 1`,
`G ≅ K₁` and `ε = 0 = ν - 1`.*  The step deletes an edge `uv`, which by theorem 2.1 is
the only `(u,v)`-path, so `ω(G - uv) = 2` by exercise 1.6.8(a); the two components are
trees on fewer vertices, and adding the edge back gives
`ε(G) = ε(G₁) + ε(G₂) + 1 = ν(G₁) + ν(G₂) - 1 = ν(G) - 1`.

**Proof.**  `hG.card_edgeFinset`, Mathlib.

**Reading.**  `ν - 1` edges is exactly the price of connecting `ν` vertices acyclically
— corollary 2.4.2 shows it is also the minimum price of connecting them at all.

**Formalisation.**  Stated additively as `ε + 1 = ν` to avoid truncated
ℕ-subtraction. -/
theorem tree_card_edgeFinset (hG : G.IsTree) :
    G.edgeFinset.card + 1 = Fintype.card V :=
  hG.card_edgeFinset

-- Cor 2.2: Every nontrivial tree has at least two vertices of degree one (leaves).
-- Mathlib: SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial (produces one such vertex)
/-- **Corollary 2.2.**  *Every nontrivial tree has at least two vertices of degree
one.*

**Book proof** (B&M §2.1).  *Let `G` be a nontrivial tree.*  Then every degree is at
least `1`, and handshaking (theorem 1.1) with theorem 2.2 gives `∑ d(v) = 2ε = 2ν - 2`
— so `ν` numbers each `≥ 1` sum to `2` less than `2ν`, forcing at least two of them to
be `1`.

**Proof.**  Three steps, all explicit here rather than imported.  (i) `hpos`: every
vertex has degree `≥ 1`, by taking a walk to some other vertex (`exists_ne` plus
`preconnected`) and reading off its first step.  (ii) `hsum`: `∑ d(v) + 2 = 2ν`, by
`omega` from `sum_degrees_eq_twice_card_edges` and `card_edgeFinset`.  (iii) `hcard`:
`by_contra` plus `Finset.sum_filter_add_sum_filter_not`, bounding the non-leaves below
by `2` via `Finset.card_nsmul_le_sum` and closing with `omega`.  Finally
`Finset.one_lt_card` extracts the two witnesses.

**Reading.**  A degree-one vertex of a tree is a **leaf**.  ⚠ B&M offer a more
illuminating alternative (exercise 2.1.2): take a longest path; both endpoints have
degree one, since an extra neighbour would either extend the path or close a cycle.
That route would be shorter in Lean too, if `exists_path_length_of_minDegree`-style
machinery from chapter 1 were available. -/
theorem tree_two_leaves (hG : G.IsTree) [Nontrivial V] :
    ∃ u v : V, u ≠ v ∧ G.degree u = 1 ∧ G.degree v = 1 := by
  classical
  -- Every vertex of a nontrivial tree has degree ≥ 1: it is connected, so some
  -- walk leaves `v`, and its first step exhibits a neighbour.
  have hpos : ∀ v : V, 1 ≤ G.degree v := by
    intro v
    obtain ⟨w, hw⟩ := exists_ne v
    obtain ⟨p⟩ := hG.isConnected.preconnected v w
    show 0 < (G.neighborFinset v).card
    cases p with
    | nil => exact absurd rfl hw
    | cons h _ => exact Finset.card_pos.mpr ⟨_, (G.mem_neighborFinset v _).mpr h⟩
  -- Handshaking (Thm 1.1) together with `ε = ν - 1` (Thm 2.2): `∑ d(v) = 2ν - 2`.
  have hsum : ∑ v, G.degree v + 2 = 2 * Fintype.card V := by
    have h1 := G.sum_degrees_eq_twice_card_edges
    have h2 := hG.card_edgeFinset
    omega
  -- `ν` numbers, each ≥ 1, summing to `2ν - 2`: at least two of them equal `1`.
  have hcard : 1 < (Finset.univ.filter (fun v => G.degree v = 1)).card := by
    by_contra hlt
    push_neg at hlt
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset V) (fun v => G.degree v = 1) (fun v => G.degree v)
    have hleaf : ∑ v ∈ Finset.univ.filter (fun v => G.degree v = 1), G.degree v
        = (Finset.univ.filter (fun v => G.degree v = 1)).card := by
      rw [Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2)]
      simp
    -- a non-leaf of a tree has degree ≥ 2
    have h2 : ∀ v ∈ Finset.univ.filter (fun v => ¬ G.degree v = 1), 2 ≤ G.degree v := by
      intro v hv
      have hne := (Finset.mem_filter.mp hv).2
      have h1 := hpos v
      omega
    have hother := Finset.card_nsmul_le_sum _ (fun v => G.degree v) 2 h2
    simp only [smul_eq_mul] at hother
    have hcards := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset V)) (p := fun v => G.degree v = 1)
    rw [Finset.card_univ] at hcards
    have hV : 2 ≤ Fintype.card V := Fintype.one_lt_card
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
  exact ⟨u, v, huv, (Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2⟩

/-! ## 2.2 Cut edges and bonds -/

/-! ### Book definitions, §2.2 (Cut edges and bonds)

*Cut edge.*  An edge `e` of `G` with `ω(G - e) > ω(G)` — deleting it strictly
increases the number of components.  Mathlib's name is `IsBridge`.

*Spanning tree.*  A spanning subgraph of `G` that is a tree.

*Edge cut and bond.*  Writing `[S, S']` for the set of edges with one end in `S`
and the other in `S'`, an **edge cut** is a set `[S, S̄]` with `S` a nonempty
proper subset of `V`.  A **bond** is a minimal nonempty edge cut; every cut edge
`e` gives the bond `{e}`.  For connected `G`, a bond is a minimal `B ⊆ E` with
`G - B` disconnected.

*Complement in `G`, cotree.*  For `H ⊆ G` the complement of `H` in `G` is
`H̄(G) = G - E(H)`.  When `T` is a spanning tree of a connected `G`, the subgraph
`T̄` is a **cotree** of `G`.

The book highlights a duality: bonds are to cotrees as cycles are to spanning
trees.  Theorem 2.6(i) mirrors "a spanning tree is acyclic" and theorem 2.6(ii)
mirrors theorem 2.5.  Chapter 12 develops this fully. -/

-- Thm 2.3: An edge is a cut edge (bridge) ⟺ it lies on no cycle of `G`.
-- Mathlib: SimpleGraph.isBridge_iff_adj_and_forall_cycle_notMem
/-- **Theorem 2.3.**  *An edge `e` of `G` is a cut edge of `G` if and only if `e`
is contained in no cycle of `G`.*

**Book proof** (B&M §2.2, verbatim).  *Let `e` be a cut edge of `G`.  Since
`ω(G-e) > ω(G)`, there exist vertices `u` and `v` of `G` that are connected in `G` but
not in `G-e`.  There is therefore some `(u,v)`-path `P` in `G` which, necessarily,
traverses `e`.  Suppose that `x` and `y` are the ends of `e`, and that `x` precedes `y`
on `P`.  In `G-e`, `u` is connected to `x` by a section of `P` and `y` is connected to
`v` by a section of `P`.  If `e` were in a cycle `C`, `x` and `y` would be connected in
`G-e` by the path `C-e`.  Thus, `u` and `v` would be connected in `G-e`, a
contradiction.*

**Proof.**  `rw [isBridge_iff_adj_and_forall_cycle_notMem]` — Mathlib's
characterisation is literally the book's statement, so the theorem is a rewrite.

**Reading.**  Cut edges are exactly the edges lying on no cycle: an edge on a cycle has
a detour around it, while an edge on no cycle is the sole link between the two sides it
joins.

**Formalisation.**  Mathlib's `IsBridge` is B&M's *cut edge*.  Note the conclusion
carries `G.Adj v w` as a conjunct, which `IsBridge` includes — a non-edge is not a
bridge. -/
theorem cutEdge_iff_no_cycle (v w : V) :
    G.IsBridge s(v, w) ↔
      G.Adj v w ∧ ∀ (u : V) (c : G.Walk u u), c.IsCycle → s(v, w) ∉ c.edges := by
  rw [isBridge_iff_adj_and_forall_cycle_notMem]

-- Thm 2.4: A connected graph is a tree ⟺ every edge is a cut edge (bridge).
-- Mathlib: SimpleGraph.isAcyclic_iff_forall_edge_isBridge
/-- **Theorem 2.4.**  *A connected graph is a tree if and only if every edge is a
cut edge.*

**Book proof** (B&M §2.2, verbatim).  *Let `G` be a tree and let `e` be an edge of
`G`.  Since `G` is acyclic, `e` is contained in no cycle of `G` and is therefore, by
theorem 2.3, a cut edge of `G`.*  Conversely a connected non-tree contains a cycle,
none of whose edges is a cut edge by theorem 2.3.

**Proof.**  Both directions go through `isAcyclic_iff_forall_edge_isBridge`: forwards
from `hT.IsAcyclic`, backwards packaging `hG` with the acyclicity it yields.

**Reading.**  A tree is exactly a connected graph with no redundancy — every single
edge indispensable for keeping it in one piece.  ⚠ Exercise 2.2.1, not stated here,
drops the connectivity hypothesis: `G` is a **forest** iff every edge is a cut
edge. -/
theorem connected_isTree_iff_forall_edge_isBridge (hG : G.Connected) :
    G.IsTree ↔ ∀ e ∈ G.edgeSet, G.IsBridge e := by
  constructor
  · -- a tree is acyclic, and in an acyclic graph every edge is a bridge (Thm 2.3)
    intro hT e he
    exact isAcyclic_iff_forall_edge_isBridge.mp hT.IsAcyclic he
  · -- conversely every-edge-a-bridge forces acyclicity, and `G` is connected by hypothesis
    intro h
    exact ⟨hG, isAcyclic_iff_forall_edge_isBridge.mpr fun e he => h e he⟩

-- Cor 2.4.1: Every connected graph contains a spanning tree.
-- Mathlib: SimpleGraph.Connected.exists_isTree_le
/-- **Corollary 2.4.1.**  *Every connected graph contains a spanning tree.*

**Book proof** (B&M §2.2, verbatim).  *Let `G` be connected and let `T` be a minimal
connected spanning subgraph of `G`.  By definition `ω(T) = 1` and `ω(T-e) > 1` for each
edge `e` of `T`.  It follows that each edge of `T` is a cut edge and therefore, by
theorem 2.4, that `T`, being connected, is a tree.*

**Proof.**  `hG.exists_isTree_le`, Mathlib.

**Reading.**  Keep deleting redundant edges — those lying on cycles — until none remain;
what is left still connects everything but has no cycle.  ★ This is the workhorse of
the rest of the chapter: corollary 2.4.2, theorem 2.6 and corollary 2.7 all open by
invoking it. -/
theorem exists_spanningTree (hG : G.Connected) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree :=
  hG.exists_isTree_le

-- Cor 2.4.2: A connected graph has ε ≥ ν − 1.
-- Mathlib: SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one
/-- **Corollary 2.4.2.**  *If `G` is connected, then `ε ≥ ν - 1`.*

**Book proof** (B&M §2.2).  *Let `G` be connected.  By corollary 2.4.1, `G` contains a
spanning tree `T`.*  Then `ε(G) ≥ ε(T) = ν - 1` by theorem 2.2.

**Proof.**  `hG.card_vert_le_card_edgeSet_add_one` gives `ν ≤ ε + 1` in `Nat.card`
form; two `Nat.card_eq_fintype_card` rewrites and `← edgeFinset_card` transfer it to
`Fintype.card`/`edgeFinset`, then `omega`.

**Reading.**  `ν - 1` edges is the minimum price of connecting `ν` vertices, and trees
are precisely the connected graphs paying exactly that price.  ⚠ Compare exercise
2.1.5, not stated here: for a graph with exactly `ν - 1` edges, connected, acyclic and
tree are all equivalent. -/
theorem connected_card_edgeFinset_ge (hG : G.Connected) :
    Fintype.card V - 1 ≤ G.edgeFinset.card := by
  -- Mathlib gives `ν ≤ ε + 1` in `Nat.card` form; transfer to `Fintype.card`/`edgeFinset`.
  have h := hG.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card] at h
  omega

-- Thm 2.5: For a spanning tree T of connected G and an edge e ∈ G, e ∉ T, `T + e` contains
-- a unique cycle.
-- NOTE: uniqueness of a cycle is only "up to rotation/reflection" and is awkward to state
-- directly, so we assert the existence half (the added edge closes a cycle); genuine
-- uniqueness is left as a `-- TODO` refinement.
/-- **Theorem 2.5.**  *Let `T` be a spanning tree of a connected graph `G` and let
`e` be an edge of `G` not in `T`.  Then `T + e` contains a unique cycle.*

**Book proof** (B&M §2.2, verbatim).  *Since `T` is acyclic, each cycle of `T+e`
contains `e`.  Moreover, `C` is a cycle of `T+e` if and only if `C-e` is a path in `T`
connecting the ends of `e`.  By theorem 2.1, `T` has a unique such path; therefore
`T+e` contains a unique cycle.*

**Skeleton** (for the existence half).
1. Write `e = s(x,y)`; `he` gives `G.Adj x y`, and `heT` that `T` lacks the edge.
2. **Theorem 2.1** gives the unique `T`-path `P` from `x` to `y` (using `hT`).
3. **Transport `P` into `T ⊔ fromEdgeSet {e}`** along the inclusion hom — `Walk.mapLe`
   or `Walk.transfer`.
4. **Close it with `e`**: `P.concat` the new edge, giving a closed walk at `x`.
5. **It is a cycle**: `P.IsPath` gives distinct internal vertices, and `heT` ensures
   `e ∉ P.edges`, so no edge repeats and the length is positive.

**Reading.**  A spanning tree already offers a unique route between the ends of `e`;
adding `e` supplies a second, and the two close off precisely one cycle — the
**fundamental cycle** of `e` with respect to `T`.  ★ The engine of the exchange
argument for Kruskal's optimality (theorem 2.10), and of chapter 12's tree-basis of the
cycle space.

**Formalisation.**  ⚠ Only the **existence** half is stated: uniqueness of a cycle in
Lean holds only up to rotation and reflection of the walk, which is awkward to phrase
directly.  Chapter 12's `fundamentalCycle` needs the uniqueness half, so this gap
propagates there. -/
theorem spanningTree_add_edge_exists_cycle
    (T : SimpleGraph V) (hT : T.IsTree) (hle : T ≤ G)
    (e : Sym2 V) (he : e ∈ G.edgeSet) (heT : e ∉ T.edgeSet) :
    ∃ (u : V) (c : (T ⊔ fromEdgeSet {e}).Walk u u), c.IsCycle := by
  sorry

-- Thm 2.6: Let T be a spanning tree of connected G and let e ∈ T.  Then
--   (i)  the cotree `Ḡ = G − E(T)` contains no bond of G;
--   (ii) `cotree + e` contains a unique bond of G.
-- The cotree edge set is `G.edgeSet \ T.edgeSet`.
/-- **Theorem 2.6.**  *Let `T` be a spanning tree of a connected graph `G`, and let
`e` be any edge of `T`.  Then (i) the cotree `T̄` contains no bond of `G`; and
(ii) `T̄ + e` contains a unique bond of `G`.*

**Book proof** (B&M §2.2, verbatim).  *(i) Let `B` be a bond of `G`.  Then `G-B` is
disconnected, and so cannot contain the spanning tree `T`.  Therefore `B` is not
contained in `T̄`.  (ii) Denote by `S` the vertex set of one of the two components of
`T-e`.  The edge cut `B = [S, S̄]` is clearly a bond of `G`, and is contained in
`T̄+e`.  Now, for any `b ∈ B`, `T-e+b` is a spanning tree of `G`.  Therefore every bond
of `G` contained in `T̄+e` must include every such element `b`.  It follows that `B` is
the only bond of `G` contained in `T̄+e`.*

**Skeleton.**
*(i).*
1. Let `B` be a bond, so `G - B` is disconnected.
2. If `B ⊆ G.edgeSet \ T.edgeSet` then `T ≤ G.deleteEdges B`, and `T` is connected and
   spanning — so `G - B` would be connected.  Contradiction.

*(ii).*
3. **Existence.**  Deleting `e` splits `T` into two components; let `S` be the vertex
   set of one.  Show `B := [S, S̄]` is a bond of `G` contained in `T̄ + e`.
4. **Uniqueness.**  For each `b ∈ B`, `T - e + b` is again a spanning tree, so any bond
   inside `T̄ + e` must contain `b` (else that spanning tree would survive its
   deletion).  Hence every such bond contains all of `B`, and minimality forces
   equality.

**Reading.**  The exact mirror of theorem 2.5, with *cycle* → *bond* and *spanning
tree* → *cotree*.  ★ Chapter 12's `fundamentalBondVertexSet` is exactly the `S` of
step 3, and cites this theorem by name.

**Formalisation.**  ⚠ Both parts consume `IsBond`, whose `∅` defect is active
here — but `hG : G.Connected` is available as a hypothesis, which is precisely the
condition under which the defect disappears.  Use it explicitly rather than relying on
it silently. -/
theorem cotree_bond
    (T : SimpleGraph V) (hT : T.IsTree) (hle : T ≤ G) (hG : G.Connected)
    (e : Sym2 V) (he : e ∈ T.edgeSet) :
    (∀ B : Set (Sym2 V), G.IsBond B → ¬ B ⊆ G.edgeSet \ T.edgeSet) ∧
      (∃! B : Set (Sym2 V), G.IsBond B ∧ B ⊆ insert e (G.edgeSet \ T.edgeSet)) := by
  sorry

/-! ## 2.3 Cut vertices -/

/-! ### Book definitions, §2.3 (Cut vertices)

*Cut vertex.*  A vertex `v` of `G` such that `E` can be partitioned into two
nonempty subsets `E₁` and `E₂` with `G[E₁]` and `G[E₂]` sharing only the vertex
`v`.  For a loopless nontrivial `G` this is equivalent to `ω(G - v) > ω(G)`.

Cut vertices are the vertex analogue of cut edges: they are the single points of
failure of a graph.  Exercise 2.3.1 relates the two notions — a connected graph
on at least three vertices with a cut edge also has a cut vertex, but not
conversely — and exercise 2.3.2 shows that a simple connected graph with exactly
two non-cut vertices must be a path. -/

-- Thm 2.7: A vertex v of a tree G is a cut vertex ⟺ d(v) > 1.
/-- **Theorem 2.7.**  *A vertex `v` of a tree `G` is a cut vertex of `G` if and
only if `d(v) > 1`.*

**Book proof** (B&M §2.3).  *If `d(v) = 0`, `G ≅ K₁` and, clearly, `v` is not a cut
vertex.*  If `d(v) = 1` then `G - v` is acyclic with `ν(G-v) - 1` edges, hence a tree
by exercise 2.1.5, so `ω(G-v) = 1 = ω(G)`.  If `d(v) > 1` then `v` has neighbours `u`,
`w`, and `uvw` is by theorem 2.1 the only `(u,w)`-path, so deleting `v` disconnects
them.

**Skeleton** (for `IsCutVertex v ↔ 1 < degree v`).  Three cases, as in the book.
1. **`d(v) = 0`.**  `hG.isConnected` on a graph with an isolated vertex forces
   `ν = 1`; then `G - v` is empty with `ω = 0`, and `1 < 0` fails.
2. **`d(v) = 1`.**  `G - v` is acyclic (a subgraph of an acyclic graph) with
   `ν - 1` vertices and `ε - 1 = ν - 2` edges, hence connected — so `ω(G-v) = 1` and
   the `<` fails.  ⚠ Needs exercise 2.1.5 (acyclic + right edge count ⟹ tree), which
   is **not** in this file and must be supplied.
3. **`d(v) > 1`.**  Take distinct neighbours `u`, `w`.  Theorem 2.1 makes `u—v—w` the
   unique `(u,w)`-path, so in `G - v` they are unreachable, giving `ω(G-v) ≥ 2 > 1`.

**Reading.**  In a tree the cut vertices are exactly the internal (non-leaf) vertices.

**Formalisation.**  ⚠ Step 2's exercise 2.1.5 is the one real import; Mathlib's
`IsAcyclic` API may supply it more directly than reproving the book's route. -/
theorem tree_isCutVertex_iff_degree (hG : G.IsTree) (v : V) :
    G.IsCutVertex v ↔ 1 < G.degree v := by
  sorry

-- Cor 2.7: Every nontrivial (loopless) connected graph has at least two non-cut vertices.
/-- **Corollary 2.7.**  *Every nontrivial loopless connected graph has at least two
vertices that are not cut vertices.*

**Book proof** (B&M §2.3, verbatim).  *Let `G` be a nontrivial loopless connected
graph.  By corollary 2.4.1, `G` contains a spanning tree `T`.  By corollary 2.2 and
theorem 2.7, `T` has at least two vertices that are not cut vertices.  Let `v` be any
such vertex.*  Then `T - v` is a connected spanning subgraph of `G - v`, so
`ω(G - v) ≤ ω(T - v) = 1 = ω(G)` and `v` is not a cut vertex of `G`.

**Skeleton** (for `∃ u v, u ≠ v ∧ ¬ IsCutVertex u ∧ ¬ IsCutVertex v`).
1. **Corollary 2.4.1** gives a spanning tree `T ≤ G`.
2. **Corollary 2.2** gives two distinct leaves `u`, `v` of `T`.
3. **Theorem 2.7** makes them non-cut-vertices *of `T`*: `ω(T - u) = 1`.
4. **Transfer to `G`.**  `T - u ≤ G - u` and adding edges can only merge components,
   so `ω(G - u) ≤ ω(T - u) = 1`; with `ω(G) = 1` this gives `¬ IsCutVertex u`.  ⚠ The
   monotonicity `H ≤ K → ω(K) ≤ ω(H)` is used here and is worth a standalone lemma —
   chapter 1's exercise 1.6.8(a) needs the same fact.

**Reading.**  However tangled a connected graph is, there are always at least two
vertices you can delete without breaking it apart. -/
theorem connected_two_non_cutVertices (hG : G.Connected) [Nontrivial V] :
    ∃ u v : V, u ≠ v ∧ ¬ G.IsCutVertex u ∧ ¬ G.IsCutVertex v := by
  sorry

/-! ## 2.4 Cayley's formula -/

/-! ### Book definitions, §2.4 (Cayley's formula)

*Contraction.*  An edge `e` of `G` is **contracted** when it is deleted and its
ends identified, giving `G · e`.  For a link `e`, `ν(G·e) = ν(G) - 1`,
`ε(G·e) = ε(G) - 1` and `ω(G·e) = ω(G)`; consequently contracting an edge of a
tree again yields a tree.

*`τ(G)`.*  The number of spanning trees of `G`.

The chapter gives a recursive formula (theorem 2.8) and, for complete graphs, a
closed one (theorem 2.9).  A determinant formula for `τ(G)` in general — the
Matrix–Tree theorem — is deferred to chapter 12. -/

-- Thm 2.8: Deletion–contraction.  For a link (non-loop edge) e, τ(G) = τ(G − e) + τ(G · e).
-- NOTE: `G · e` uses the stubbed `contract` above (same-carrier placeholder); the intended
-- statement is over the true contracted graph on `ν − 1` vertices.
/-- **Theorem 2.8** (deletion–contraction).  *If `e` is a link of `G`, then
`τ(G) = τ(G - e) + τ(G · e)`.*

**Book proof** (B&M §2.4, verbatim).  *Since every spanning tree of `G` that does not
contain `e` is also a spanning tree of `G-e`, and conversely, `τ(G-e)` is the number of
spanning trees of `G` that do not contain `e`.*  Contracting `e` inside a spanning tree
that *does* contain it gives a bijection with the spanning trees of `G · e`, so those
number `τ(G·e)`; adding the two counts gives the recursion.

**Skeleton** (for `τ(G) = τ(G-e) + τ(G·e)`).
1. **Partition** the spanning trees of `G` by whether they contain `e`.
2. **The `e`-avoiding ones biject with spanning trees of `G - e`** — the identity map,
   since a tree avoiding `e` is a subgraph of `G - e` and conversely.
3. **The `e`-containing ones biject with spanning trees of `G · e`** via contraction.
   This is the substantial half and is where the carrier change matters.
4. `Nat.card_sum` on the partition.

**Reading.**  Iterating the recursion reduces any graph to trivial ones and so computes
`τ` — though B&M note it is impractical for large graphs, which is what motivates
chapter 12's determinant formula.

**⚠ Currently vacuous.**  `contract` has a `sorry` body, so `G · e` is opaque and this
statement relates opaque quantities.  Worse, `contract` is a **same-carrier**
placeholder, so even an honest body on `V` could not satisfy `ν(G·e) = ν - 1` and step
3's bijection would be false.  Repair `contract` on the quotient carrier first — see its
docstring. -/
theorem numSpanningTrees_deletion_contraction (e : Sym2 V) (he : e ∈ G.edgeSet) :
    G.numSpanningTrees =
      (G.deleteEdges {e}).numSpanningTrees + (G.contract e).numSpanningTrees := by
  sorry

-- Thm 2.9 (Cayley): τ(Kₙ) = n^(n−2).
-- Mathlib has no Cayley's formula; `⊤ : SimpleGraph (Fin n)` is the complete graph Kₙ.
/-- **Theorem 2.9** (Cayley's formula).  *`τ(Kₙ) = n^(n-2)`.*

**Book proof** (B&M §2.4, verbatim).  *Let the vertex set of `Kₙ` be
`N = {1, 2, …, n}`.  We note that `n^{n-2}` is the number of sequences of length `n-2`
that can be formed from `N`.  Thus, to prove the theorem, it suffices to establish a
one–one correspondence between the set of spanning trees of `Kₙ` and the set of such
sequences.*

*Tree to sequence.*  Let `s₁` be the first vertex of degree one in `T` and `t₁` its
unique neighbour; delete `s₁`, let `s₂` be the first degree-one vertex of `T - s₁` and
`t₂` its neighbour; repeat until `t_{n-2}` is defined and two vertices remain.  This is
the **Prüfer sequence**.

*Sequence to tree.*  Any `v` occurs exactly `d_T(v) - 1` times, so the leaves are
precisely the vertices never appearing.  Let `s₁` be the first vertex of `N` not in
`(t₁, …, t_{n-2})` and join it to `t₁`; let `s₂` be the first vertex of `N \ {s₁}` not
in `(t₂, …, t_{n-2})` and join it to `t₂`; continue, finally joining the two remaining
vertices.  The two constructions are mutually inverse.

**⚠ Statement defect: false at `n = 0`.**  On `Fin 0` there is no tree at all —
`IsTree` bundles `Connected`, which requires `Nonempty` — so `τ = 0`.  But
`0 ^ (0 - 2) = 0 ^ 0 = 1` in ℕ, since `0 - 2` truncates to `0`.  So the claim reads
`0 = 1`.  *The repair* is a hypothesis `1 ≤ n` (or `n ≠ 0`); `n = 1` and `n = 2` are
both fine (`τ = 1 = n^0`).

**Skeleton** (for `τ(Kₙ) = n^(n-2)`, assuming `1 ≤ n`).
1. **Build the Prüfer map** `spanning trees of Kₙ → (Fin (n-2) → Fin n)` by the
   recursion above.  Termination: each step deletes a vertex.
2. **Build the inverse** by the reconstruction above.
3. **Prove the round trips** — the bulk of the work, and genuinely long.
4. `Nat.card_congr` on the bijection, then `Fintype.card_fun`.

**Reading.**  ⚠ B&M caution that `n^{n-2}` counts *distinct* spanning trees, not
non-isomorphic ones: `K₆` has six non-isomorphic ones but `6⁴ = 1296` distinct.

**Formalisation.**  Mathlib has no Cayley formula and no Prüfer correspondence, so all
four steps are from scratch — the largest single item in the chapter. -/
theorem cayley (n : ℕ) :
    numSpanningTrees (⊤ : SimpleGraph (Fin n)) = n ^ (n - 2) := by
  sorry

/-! ## 2.5 The connector problem (Kruskal) -/

/-! ### Book content, §2.5 (The connector problem)

*The problem.*  A railway network connecting a number of towns is to be built,
with a known cost `c_ij` of a direct link between towns `vᵢ` and `vⱼ`; design the
network so as to minimise total construction cost.  Modelling towns as vertices
of a weighted graph with `w(vᵢvⱼ) = c_ij`, this asks for a minimum-weight
connected spanning subgraph.  Costs being non-negative, such a subgraph may be
taken to be a spanning tree; a minimum-weight spanning tree is called an
**optimal tree**.

*Kruskal's algorithm.*  Choose a link `e₁` of smallest possible weight.  Having
chosen `e₁, …, eᵢ`, choose `e_{i+1}` from the remaining edges so that
(i) `G[{e₁, …, e_{i+1}}]` is acyclic and (ii) subject to (i), `w(e_{i+1})` is as
small as possible.  Stop when no further edge can be chosen.  The greedy choice
works because a maximal acyclic subgraph of a connected graph is a spanning tree.

*Theorem 2.10.*  Any spanning tree `T* = G[{e₁, …, e_{ν-1}}]` constructed by
Kruskal's algorithm is an optimal tree.  The proof is an exchange argument: among
optimal trees choose `T` maximising `f(T)`, the least index `i` with `eᵢ ∉ T`.
If `f(T) = k`, then `T + e_k` contains a unique cycle `C` (theorem 2.5); pick an
edge `e_k'` of `C` lying in `T` but not `T*`.  By theorem 2.3 `e_k'` is not a cut
edge of `T + e_k`, so `T' = (T + e_k) - e_k'` is another spanning tree, with
`w(T') = w(T) + w(e_k) - w(e_k')`.  Kruskal's greedy choice forces
`w(e_k') ≥ w(e_k)`, hence `w(T') ≤ w(T)` and `T'` is also optimal — but
`f(T') > f(T)`, contradicting the choice of `T`.

*Efficiency.*  Sorting the edges costs about `ε log ε` steps, the acyclicity
tests `ε` comparisons, and the component relabelling `ν(ν-1)`; so Kruskal's
algorithm is a good algorithm in the sense of §1.8. -/

open scoped Classical in
-- Thm 2.10 (Kruskal optimality): the output of Kruskal's algorithm is an optimal
-- (minimum-weight) spanning tree.
-- NOTE: Kruskal's algorithm itself is procedural.  We state the mathematical target it
-- attains: among all spanning trees of a connected weighted graph there is one of minimum
-- total edge weight.
/-- **Theorem 2.10** (Kruskal optimality), stated as an existence result.
*Among all spanning trees of a connected weighted graph there is one of minimum
total edge weight — an optimal tree — and Kruskal's algorithm constructs one.*

**Book proof** (B&M §2.5).  *By contradiction.  For any spanning tree `T` of `G` other
than `T*`, denote by `f(T)` the smallest value of `i` such that `eᵢ` is not in `T`.  Now
assume that `T*` is not an optimal tree, and let `T` be an optimal tree such that
`f(T)` is as large as possible.*  If `f(T) = k`, then `T + e_k` contains a unique cycle
`C` (theorem 2.5); pick an edge `e_k'` of `C` in `T` but not `T*`.  By theorem 2.3
`e_k'` is not a cut edge of `T + e_k`, so `T' = (T + e_k) - e_k'` is a spanning tree
with `w(T') = w(T) + w(e_k) - w(e_k')`.  Kruskal's greedy choice forces
`w(e_k') ≥ w(e_k)`, so `w(T') ≤ w(T)` and `T'` is also optimal — but `f(T') > f(T)`,
contradicting the choice of `T`.

**Skeleton** (for the existence form actually stated).
1. **Corollary 2.4.1** gives at least one spanning tree, so the family is nonempty.
2. **The family is finite** — spanning trees are subgraphs of `G` on a `Fintype`
   carrier, so `{T // T ≤ G ∧ T.IsTree}` is finite.
3. **A minimum is attained**: `Finset.exists_min_image` on the weight function.
4. Read off the three conjuncts.

**Reading.**  Assign each edge a weight and each spanning tree the total; the connector
problem asks for the least, and theorem 2.10 guarantees Kruskal's greedy procedure —
repeatedly take the cheapest edge not closing a cycle — always finds one.

**Formalisation.**  ⚠ The algorithm is a *procedure*, not a proposition, so what is
stated is the mathematical target it attains: **existence** of a minimum-weight
spanning tree.  That is strictly weaker than theorem 2.10, which asserts the *greedy
output* is optimal — the exchange argument quoted above is not exercised by the
skeleton, which is a three-line finiteness argument instead.  Formalising the real
theorem would need Kruskal's algorithm defined first.  Weights are `ℝ`-valued, matching
B&M's remark that the algorithm is valid for arbitrary real weights. -/
theorem exists_min_weight_spanningTree (hG : G.Connected) (w : Sym2 V → ℝ) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧
      ∀ T' : SimpleGraph V, T' ≤ G → T'.IsTree →
        ∑ e ∈ T.edgeFinset, w e ≤ ∑ e ∈ T'.edgeFinset, w e := by
  sorry

end SimpleGraph
