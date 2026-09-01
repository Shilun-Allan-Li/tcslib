import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Partition
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Bondy & Murty, *Graph Theory with Applications* — Chapter 8: Vertex Colourings

Sorry-skeleton extracted from `papers/bondy-murty-ch8-vertex-colourings.md`.

Every proof body is `sorry`; this file is a scaffold for sorry-driven development (fill one stub
at a time, `lake build` after each).  Mathlib supplies the *vocabulary* of the chapter
(`Coloring`, `Colorable`, `chromaticNumber : ℕ∞`) but **not one theorem of it**, so every result
below is a genuine build.  The `⚠ MISSING` primitives the chapter needs (`IsCritical`,
`contractEdge`, `HasK4Subdivision`, `mycielskian`, the join, …) are defined locally with honest
bodies — never `sorry` in a `def`.  The outline's `import TCSlib.*` lines refer to repo files that
are not needed here; the connectivity notions the chapter uses (`IsVertexCut`, `edgeConnectivity`)
are re-defined locally, mirroring `TCSlib/GraphTheory/Connectivity.lean`.

NOTE: `chromaticNumber` is `ℕ∞`-valued (`Coloring.lean:167`), so additive/subtractive statements
are phrased to respect that (extract to `ℕ`, or state with `≤`/`=`).  `numColorings` (= `π_k`) is
defined with `Nat.card` rather than the outline's `Fintype.card`: the two agree over a `Fintype`,
and `Nat.card` lets the §8.4 statements elaborate on `Subgraph`/component carriers with no bespoke
`Fintype` instance.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Key Definitions -/

/-- A **vertex cut** `S`: a subset whose deletion leaves `G` disconnected.

**Book definition** (B&M §3.1, verbatim).  *A vertex cut of `G` is a subset `V'`
of `V` such that `G - V'` is disconnected.  A `k`-vertex cut is a vertex cut of
`k` elements.*

**Reading.**  Deleting `V'` breaks the graph into pieces that no longer
communicate with one another.  Vertex cuts are this chapter's main structural
tool: theorem 8.2 says a critical graph has no *clique* vertex cut, corollary 8.2
reads off the case `|S| = 1` (a critical graph has no cut vertex), and theorem
8.3 analyses in detail what survives at `|S| = 2`.

**Formalisation.**  Mirrors `TCSlib/GraphTheory/Connectivity.lean` (the repo's
`Connectivity/Defs.lean:42`).  The conjunct `↑S ⊂ Set.univ` is not decoration: it
excludes `S = V`, where `G - V'` has empty carrier.  Mathlib's `Connected`
carries a `Nonempty` field, so the empty graph counts as disconnected and without
this guard *every* graph would have `V` itself as a vertex cut. -/
def IsVertexCut (G : SimpleGraph V) (S : Finset V) : Prop :=
  (↑S : Set V) ⊂ Set.univ ∧ ¬ (G.induce ((↑S : Set V)ᶜ)).Connected

/-- An **edge cut** `F`: a set of edges whose deletion leaves `G` disconnected.

**Book definition** (B&M §3.1, verbatim).  *Recall that an edge cut of `G` is a
subset of `E` of the form `[S, S̄]`, where `S` is a nonempty proper subset of
`V`.  A `k`-edge cut is an edge cut of `k` elements.  If `G` is nontrivial and
`E'` is an edge cut of `G`, then `G - E'` is disconnected.*

**Reading.**  Pick a nonempty proper set `S` of vertices and take every edge with
one end in `S` and the other outside; removing those edges severs `S` from the
rest.  Needed here by exercise 8.1.13(b) (Dirac): every `k`-critical graph is
`(k-1)`-edge-connected.

**Formalisation.**  The book defines an edge cut *by its shape* `[S, S̄]` and then
observes that deleting one disconnects a nontrivial graph.  This definition takes
the observation as the condition instead — `F ⊆ edgeSet` with
`G.deleteEdges F` disconnected — which is the repo's notion
(`Connectivity/Defs.lean`) and the one exercise 8.1.13(b) actually consumes.  The
two agree on the quantity that matters below: the minimum size of such an `F` is
the same either way, since every disconnecting set of edges contains a `[S, S̄]`
for `S` a component of the remainder. -/
def IsEdgeCut (G : SimpleGraph V) (F : Finset (Sym2 V)) : Prop :=
  (↑F : Set (Sym2 V)) ⊆ G.edgeSet ∧ ¬ (G.deleteEdges (↑F : Set (Sym2 V))).Connected

open scoped Classical in
/-- Edge connectivity `κ'(G)`: the minimum size of an edge cut.

**Book definition** (B&M §3.1, verbatim).  *We … define the edge connectivity
`κ'(G)` of `G` to be the minimum `k` for which `G` has a `k`-edge cut.  If `G` is
trivial, `κ'(G)` is defined to be zero.  Thus `κ'(G) = 0` if `G` is either
trivial or disconnected, and `κ'(G) = 1` if `G` is a connected graph with a cut
edge.  `G` is said to be `k`-edge-connected if `κ'(G) ≥ k`.*

**Reading.**  The least number of edges one must cut to break the graph apart —
a measure of how robustly it holds together.  Exercise 8.1.13(b) shows criticality
forces this to be large: a `k`-critical graph is `(k-1)`-edge-connected.

**Formalisation.**  Mirrors the repo's `edgeConnectivity`
(`Connectivity/Defs.lean:72`).  `sInf ∅ = 0` in `ℕ`, so the book's separate
convention for the trivial graph comes out automatically: with no edge cut
available the infimum is taken over the empty set and yields `0`. -/
noncomputable def edgeConnectivity (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ F : Finset (Sym2 V), G.IsEdgeCut F ∧ F.card = n}

/-- `G` is **critical**: `χ(H) < χ(G)` for every proper subgraph `H ⊂ G`.
⚠ MISSING from Mathlib.

**Book definition** (B&M §8.1, verbatim).  *It is helpful, when dealing with
colourings, to study the properties of a special class of graphs called critical
graphs.  We say that a graph `G` is critical if `χ(H) < χ(G)` for every proper
subgraph `H` of `G`.  Such graphs were first investigated by Dirac (1952).*

**Reading.**  A critical graph is "minimally" `k`-chromatic: remove any vertex or
any edge and the chromatic number drops.  Critical graphs are useful precisely
because they carry the whole difficulty of a colouring problem — every
`k`-chromatic graph contains a `k`-critical subgraph, so statements about
`k`-chromatic graphs reduce to the critical case, which is how corollary 8.1.1,
Brooks' theorem 8.4 and theorem 8.5 all begin.

**Formalisation.**  The quantifier ranges over `G.Subgraph`, not over the order
on `SimpleGraph V`.  This is load-bearing (Scaffolding judgement 1): the
`SimpleGraph V` order can only *remove edges*, never vertices, whereas the book's
"proper subgraph" includes `G - v`.  Under the weaker order `⊥` on two vertices
would be vacuously 1-critical — it has no proper edge-subgraph — contradicting
exercise 8.1.7, which says the only 1-critical graph is `K₁`. -/
def IsCritical {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ H : G.Subgraph, H < ⊤ → H.coe.chromaticNumber < G.chromaticNumber

/-- `G` is `k`-**critical**: `k`-chromatic and critical.

**Book definition** (B&M §8.1, verbatim).  *A `k`-critical graph is one that is
`k`-chromatic and critical; every `k`-chromatic graph has a `k`-critical
subgraph.  A 4-critical graph, due to Grötzsch (1958), is shown in figure 8.2.*

**Reading.**  `k`-critical graphs are the irreducible witnesses to needing `k`
colours.  Exercise 8.1.7 classifies the small cases completely — the only
1-critical graph is `K₁`, the only 2-critical graph is `K₂`, and the 3-critical
graphs are exactly the odd cycles — and Brooks' theorem 8.4 consumes precisely
that classification to get its standing hypothesis `k ≥ 4`.

**Formalisation.**  `G.chromaticNumber = k` compares an `ℕ∞` with a coerced `ℕ`,
so `k`-chromaticity here also carries the information that `χ(G) ≠ ⊤`. -/
def IsKCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = k ∧ G.IsCritical

/-- `G · uv`: contract the edge `uv` by identifying `v` into `u`.  Carrier drops to `{x // x ≠ v}`.
⚠ MISSING from Mathlib (`replaceVertex` is a *different* operation).

**Book definition** (B&M §2.4, verbatim; used in §8.3 and §8.4).  *An edge `e` of
`G` is said to be contracted if it is deleted and its ends are identified; the
resulting graph is denoted by `G · e`.*

Theorem 8.3(ii) restates it locally: *`G₂ · uv` denotes the graph obtained from
`G₂` by identifying `u` and `v`.*

**Reading.**  Pull the edge `uv` tight until `u` and `v` merge into a single
vertex, which inherits the neighbours of both.  Contraction appears twice in this
chapter: in theorem 8.3, where `G₂ · uv` is shown to be `k`-critical, and in
theorem 8.6, the deletion–contraction recursion for the chromatic polynomial —
which the book notes *bears a close resemblance to the recursion formula for
`τ(G)`* in theorem 2.8.

**Formalisation.**  Identification is realised by *dropping* `v` from the carrier
and re-pointing its edges at `u`, so the carrier is `{x : V // x ≠ v}` and the
merged vertex is `u`.  The `a ≠ b` conjunct in `Adj` restores looplessness: the
book's contraction of a multigraph may create loops and parallel edges, and
taking the underlying simple graph is exactly what discarding them means.  This
is harmless for both uses — theorem 8.6 is stated for simple `G`, and colourings
never see loops or multiplicities. -/
def contractEdge {V : Type*} (G : SimpleGraph V) (u v : V) :
    SimpleGraph {x : V // x ≠ v} where
  Adj a b := a ≠ b ∧ (G.Adj a.1 b.1 ∨ (a.1 = u ∧ G.Adj v b.1) ∨ (b.1 = u ∧ G.Adj a.1 v))
  symm := by
    rintro a b ⟨hab, h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
    · exact ⟨hab.symm, Or.inl h.symm⟩
    · exact ⟨hab.symm, Or.inr (Or.inr ⟨h₁, h₂.symm⟩)⟩
    · exact ⟨hab.symm, Or.inr (Or.inl ⟨h₁, h₂.symm⟩)⟩
  loopless := by rintro a ⟨h, -⟩; exact h rfl

/-- `π_k(G)`, the number of distinct proper `k`-colourings.  NOT a missing def.

**Book definition** (B&M §8.4, verbatim).  *We shall denote the number of distinct
`k`-colourings of `G` by `π_k(G)`; thus `π_k(G) > 0` if and only if `G` is
`k`-colourable.  Two colourings are to be regarded as distinct if some vertex is
assigned different colours in the two colourings; in other words, if
`(V₁, V₂, …, V_k)` and `(V₁', V₂', …, V_k')` are two colourings, then
`(V₁, V₂, …, V_k) = (V₁', V₂', …, V_k')` if and only if `Vᵢ = Vᵢ'` for
`1 ≤ i ≤ k`.  For example, a triangle has the six distinct 3-colourings shown in
figure 8.7.  Note that even though there is exactly one vertex of each colour in
each colouring, we still regard these six colourings as distinct.*

The book then records the two anchoring cases: *If `G` is empty, then each vertex
can be independently assigned any one of the `k` available colours.  Therefore
`π_k(G) = k^ν`.  On the other hand, if `G` is complete, then there are `k` choices
of colour for the first vertex, `k-1` choices for the second, `k-2` for the third,
and so on.  Thus, in this case, `π_k(G) = k(k-1)…(k-ν+1)`.*

**Reading.**  Count the proper colourings as *labelled* objects, not up to
permutation of the colours — the triangle example is exactly the warning against
quotienting.  Birkhoff (1912) introduced this counting approach as a possible
route to the four-colour conjecture.

**Formalisation.**  `Nat.card (G.Coloring (Fin k))` rather than `Fintype.card`:
the two agree over a `Fintype`, but `Nat.card` needs no instance, which lets the
§8.4 statements elaborate over `Subgraph` and component carriers without bespoke
`Fintype` derivations.  A `G.Coloring (Fin k)` is a function on vertices, so
distinctness is pointwise — precisely the book's criterion. -/
noncomputable def numColorings {V : Type*} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card (G.Coloring (Fin k))

/-- A `{u,v}`-component: `G[C ∪ {u,v}]` for `C` a component of `G − {u,v}`.  ⚠ MISSING.

**Book definition** (B&M §8.1, verbatim).  *Let `S` be a vertex cut of a connected
graph `G`, and let the components of `G - S` have vertex sets `V₁, V₂, …, V_n`.
Then the subgraphs `Gᵢ = G[Vᵢ ∪ S]` are called the `S`-components of `G` (see
figure 8.3).  We say that colourings of `G₁, G₂, …, G_n` agree on `S` if, for
every `v ∈ S`, vertex `v` is assigned the same colour in each of the colourings.*

(The source prints `Gᵢ = G[V ∪ S]`; `V` there is an OCR slip for `Vᵢ`, as the
surrounding text and figure 8.3 make clear.)

**Reading.**  Cut the graph at `S` and put `S` back onto each resulting piece, so
the pieces overlap in exactly `S`.  A colouring of `G` is then the same thing as a
family of colourings of the `S`-components that *agree on `S`* — that equivalence
is the entire mechanism behind theorems 8.2 and 8.3, both of which proceed by
colouring the pieces separately and then trying to reconcile them on `S`.

**Formalisation.**  Only the case `S = {u, v}` is needed (theorem 8.3), so the
definition is specialised to it and indexed by a connected component `c` of
`G - {u,v}` rather than by a numeral `i`.  The result is a `G.Subgraph`, which is
what lets theorem 8.3(i) state `G = G₁ ∪ G₂` as a `⊔` in the subgraph lattice. -/
def uvComponent {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u v : V)
    (c : (G.induce ({u, v}ᶜ : Set V)).ConnectedComponent) : G.Subgraph :=
  (⊤ : G.Subgraph).induce ((Subtype.val '' c.supp) ∪ {u, v})

/-- Type 1: **every** `(k-1)`-colouring assigns `u` and `v` the same colour.  ⚠ MISSING.

**Book definition** (B&M §8.1, verbatim).  *We shall say that a `{u, v}`-component
`Gᵢ` of `G` is of type 1 if every `(k-1)`-colouring of `Gᵢ` assigns the same
colour to `u` and `v`* …

**Reading.**  The component forces `u` and `v` to agree.  The quantifier is
universal — not that *some* colouring identifies them, but that *no* colouring can
separate them.  This is only interesting because `u` and `v` are nonadjacent in a
critical graph (the consequence of theorem 8.2 recorded below), so a priori a
colouring is free to do either.

**Formalisation.**  Stated for a `G.Subgraph` `H` with explicit membership proofs
`hu`, `hv`, since `H.coe` lives on `H.verts` and `u`, `v` must be named as
elements of it.  `Fin (k - 1)` uses ℕ-subtraction; every use site has `k ≥ 2`, so
no truncation occurs. -/
def Subgraph.IsType1 {V : Type*} {G : SimpleGraph V} (H : G.Subgraph)
    (u v : V) (hu : u ∈ H.verts) (hv : v ∈ H.verts) (k : ℕ) : Prop :=
  ∀ C : H.coe.Coloring (Fin (k - 1)), C ⟨u, hu⟩ = C ⟨v, hv⟩

/-- Type 2: **every** `(k-1)`-colouring assigns `u` and `v` different colours.  ⚠ MISSING.

**Book definition** (B&M §8.1, verbatim).  … *and of type 2 if every
`(k-1)`-colouring of `Gᵢ` assigns different colours to `u` and `v` (see figure
8.4).*

**Reading.**  The component forces `u` and `v` to disagree.  A type-1 component
and a type-2 component make irreconcilable demands, so their union admits no
`(k-1)`-colouring at all — which is exactly the contradiction driving theorem 8.3,
and the reason a critical graph with a 2-vertex cut has precisely two pieces, one
of each type.

**Formalisation.**  As for `IsType1`.  Note that "type 1" and "type 2" are not
exhaustive: a component may admit both kinds of `(k-1)`-colouring and be of
neither type.  Theorem 8.3 has to *prove* that the two pieces it produces are of
opposite types; it is not true by definition. -/
def Subgraph.IsType2 {V : Type*} {G : SimpleGraph V} (H : G.Subgraph)
    (u v : V) (hu : u ∈ H.verts) (hv : v ∈ H.verts) (k : ℕ) : Prop :=
  ∀ C : H.coe.Coloring (Fin (k - 1)), C ⟨u, hu⟩ ≠ C ⟨v, hv⟩

/-- `G` contains a **subdivision of `K₄`**: four distinct branch vertices joined pairwise by six
paths, internally disjoint from each other and internally avoiding all four branch vertices.
⚠ MISSING from Mathlib.

**Book definition** (B&M §8.3, verbatim).  *A subdivision of a graph `G` is a graph
that can be obtained from `G` by a sequence of edge subdivisions.  A subdivision of
`K₄` is shown in figure 8.5.*

The underlying operation is §3.2: *An edge `e` is said to be subdivided when it is
deleted and replaced by a path of length two connecting its ends, the internal
vertex of this path being a new vertex.*

The book states Hajós' conjecture (1961) in the same paragraph: *if `G` is
`k`-chromatic, then `G` contains a subdivision of `K_k`* — adding that *the
condition is not sufficient; for example, a 4-cycle is a subdivision of `K₃`, but
is not 3-chromatic*, and that `k = 1, 2` are obvious while `k = 3` holds *because
a 3-chromatic graph necessarily contains an odd cycle, and every odd cycle is a
subdivision of `K₃`*.  Theorem 8.5 (Dirac, 1952) settles `k = 4`.

**Reading.**  A "topological `K₄`": four **branch vertices**, each of the six pairs
joined by a path, the six paths sharing no interior vertices with one another or
with the branch vertices.  Drawn on paper it is `K₄` with beads threaded onto its
edges.

**Formalisation.**  The book says "obtainable from `K₄` by subdividing edges",
which is a statement about an abstract graph; what a *containment* claim needs is
the witness form above — six `Walk`s in `G` with disjointness conditions.  The two
are equivalent, and only this direction is ever used.  The three side conditions
say, in order: the branch vertices are distinct; each of the six walks is a path;
no path's interior meets a branch vertex; and no two paths' interiors meet.
`support.tail.dropLast` is the interior of a walk (drop both endpoints). -/
def HasK4Subdivision {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (a b c d : V) (pab : G.Walk a b) (pac : G.Walk a c) (pad : G.Walk a d)
    (pbc : G.Walk b c) (pbd : G.Walk b d) (pcd : G.Walk c d),
    [a, b, c, d].Nodup ∧
    (pab.IsPath ∧ pac.IsPath ∧ pad.IsPath ∧ pbc.IsPath ∧ pbd.IsPath ∧ pcd.IsPath) ∧
    (∀ p ∈ [pab.support.tail.dropLast, pac.support.tail.dropLast, pad.support.tail.dropLast,
            pbc.support.tail.dropLast, pbd.support.tail.dropLast, pcd.support.tail.dropLast],
       ∀ x ∈ p, x ∉ ({a, b, c, d} : Set V)) ∧
    (List.Pairwise (fun p q => ∀ x ∈ p, x ∉ q)
      [pab.support.tail.dropLast, pac.support.tail.dropLast, pad.support.tail.dropLast,
       pbc.support.tail.dropLast, pbd.support.tail.dropLast, pcd.support.tail.dropLast])

/-- **Mycielski's construction** on `V ⊕ V ⊕ Unit`: `inl` = the old graph, `inr ∘ inl` = the
shadows `uᵢ` (joined to `vᵢ`'s neighbours), `inr ∘ inr` = the apex (joined to every shadow).
⚠ MISSING from Mathlib.

**Book construction** (B&M §8.5, Mycielski 1955, verbatim).  *Suppose that we have
already constructed a triangle-free graph `G_k` with chromatic number `k ≥ 2`.
Let the vertices of `G_k` be `v₁, v₂, …, v_n`.  Form a new graph `G_{k+1}` from
`G_k` as follows: add `n+1` new vertices `u₁, u₂, …, u_n, v`, and then, for
`1 ≤ i ≤ n`, join `uᵢ` to the neighbours of `vᵢ` and to `v`.  For example, if `G₂`
is `K₂` then `G₃` is the 5-cycle and `G₄` the Grötzsch graph (see figure 8.10).*

**Reading.**  Each original vertex `vᵢ` gets a **shadow** `uᵢ` attached to `vᵢ`'s
neighbourhood but *not* to `vᵢ` itself, and a single **apex** `v` is joined to all
the shadows.  The construction preserves triangle-freeness while raising the
chromatic number by exactly one; starting from `K₂` it yields the 5-cycle, then
the Grötzsch graph, and in general a triangle-free `k`-chromatic graph on
`3·2^{k-2} - 1` vertices.  Theorem 8.7 is the proof that it does this.

**Formalisation.**  Carrier `V ⊕ V ⊕ Unit`: `inl a` is the original `v_a`,
`inr (inl a)` its shadow `u_a`, `inr (inr ())` the apex.  Reading the `Adj` match
against the book: `inl`–`inl` copies `G`; `inl`–`inr ∘ inl` joins `u_a` to the
neighbours of `v_a` (note `G.Adj a b`, not `a = b`, so `u_a` is *not* joined to
`v_a`); `inr ∘ inl`–`inr ∘ inr` joins every shadow to the apex.  Everything else
is `False`, which in particular leaves the shadows independent and the apex
nonadjacent to the original vertices. -/
def mycielskian {V : Type*} (G : SimpleGraph V) : SimpleGraph (V ⊕ V ⊕ Unit) where
  Adj
    | .inl a,        .inl b        => G.Adj a b
    | .inl a,        .inr (.inl b) => G.Adj a b
    | .inr (.inl a), .inl b        => G.Adj a b
    | .inr (.inl _), .inr (.inr _) => True
    | .inr (.inr _), .inr (.inl _) => True
    | _,             _             => False
  symm := by rintro (a | a | a) (b | b | b) <;> simp_all [G.adj_comm]
  loopless := by rintro (a | a | a) <;> simp

/-- B&M's **join** `G₁ ∨ G₂`: disjoint union plus all cross edges.  ⚠ NOT a missing primitive.

**Book definition** (B&M §4.2, verbatim; used in exercises 8.1.10 and 8.4.5).  *We
first introduce the notion of the join of two graphs.  The join `G ∨ H` of
disjoint graphs `G` and `H` is the graph obtained from `G + H` by joining each
vertex of `G` to each vertex of `H`; it is represented diagrammatically as in
figure 4.8.*

**Reading.**  Lay the two graphs side by side and add every possible edge between
them.  No colour can then be shared across the join, so the chromatic numbers
simply add: `χ(G₁ ∨ G₂) = χ(G₁) + χ(G₂)` (exercise 8.1.10(a)), and criticality is
inherited from both factors (8.1.10(b)).

**Formalisation.**  One line, no new primitive: `G + H` is Mathlib's
`SimpleGraph.sum` (`⊕g`) on `α ⊕ β`, and "join each vertex of `G` to each vertex
of `H`" is exactly `completeBipartiteGraph α β`, so the join is their `⊔`.  An
`abbrev`, so it unfolds and the `⊔`/`⊕g` simp sets stay available. -/
abbrev join {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) :
    SimpleGraph (α ⊕ β) := (G ⊕g H) ⊔ completeBipartiteGraph α β

/-- The **wheel** with `n` spokes: `C_n ∨ K₁`.

**Book definition** (B&M exercise 2.4.2, verbatim; used in exercise 8.4.5(b)).  *A
wheel is a graph obtained from a cycle by adding a new vertex and edges joining it
to all the vertices of the cycle; the new edges are called the spokes of the
wheel.*

**Reading.**  A hub joined to every vertex of a rim cycle.  As a join `C_n ∨ K₁`
it inherits `χ = χ(C_n) + 1` from exercise 8.1.10(a), so a wheel with an odd rim
is 4-chromatic and one with an even rim is 3-chromatic.  Exercise 8.4.5(b)
computes its chromatic polynomial.

**Formalisation.**  "`n` spokes" means `n` rim vertices, so the rim is
`cycleGraph n` and the hub is the unique vertex of `⊤ : SimpleGraph Unit`.  Since
`join` adds *all* cross edges and the hub side is a single vertex, the added edges
are exactly the `n` spokes. -/
abbrev wheel (n : ℕ) : SimpleGraph (Fin n ⊕ Unit) :=
  (cycleGraph n).join (⊤ : SimpleGraph Unit)

/-- `G` is **uniquely `k`-colourable**: any two `k`-colourings induce the same partition.
⚠ MISSING.

**Book definition** (B&M exercise 8.1.8, verbatim).  *A graph `G` is uniquely
`k`-colourable if any two `k`-colourings of `G` induce the same partition of `V`.*

**Reading.**  Colours are arbitrary labels, so what a colouring really determines
is the partition into colour classes.  `G` is uniquely `k`-colourable when that
partition is forced — two `k`-colourings can then differ only by renaming the
colours.  Complete graphs are the obvious examples, which is why exercise 8.1.8
(no vertex cut of a `k`-critical graph induces a uniquely `(k-1)`-colourable
subgraph) generalises theorem 8.2 (no vertex cut is a clique).

**Formalisation.**  `Coloring.colorClasses` is the induced partition, so the book's
"induce the same partition" is a literal equality of `colorClasses`.  Note this is
vacuously true when `G` has no `k`-colouring at all; every use site supplies
colourability separately. -/
def UniquelyColorable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ C C' : G.Coloring (Fin k), C.colorClasses = C'.colorClasses

/-- `s` is a **maximal independent set** of `G` within `t`.

**Book context** (B&M §8.6, verbatim).  *Since the chromatic number of a graph is
the least number of independent sets into which its vertex set can be partitioned,
we begin by describing a method for listing all the independent sets in a graph.
Because every independent set is a subset of a maximal independent set, it
suffices to determine all the maximal independent sets.*

**Reading.**  `s` is independent, lies inside `t`, and cannot be enlarged *within
`t`* without losing independence.

**Formalisation.**  The book only ever says "maximal independent set of `G - X`"
for various `X`.  Rather than form the deleted graph, this relativises: `t` is the
ambient set, and maximality is tested against subsets of `t`.  Taking
`t = Set.univ` recovers the plain notion.  This is the shape
`IsCanonicalColouring` needs, where each colour class must be maximal in what
remains after the earlier classes are removed. -/
def IsMaximalIndepSetIn {V : Type*} (G : SimpleGraph V) (s t : Set V) : Prop :=
  s ⊆ t ∧ G.IsIndepSet s ∧ ∀ u, s ⊂ u → u ⊆ t → ¬ G.IsIndepSet u

/-- A **canonical colouring**, as a list of colour classes.  ⚠ MISSING.

**Book definition** (B&M §8.6, verbatim).  *A `k`-colouring `(V₁, V₂, …, V_k)` of
`G` is said to be canonical if `V₁` is a maximal independent set of `G`, `V₂` is a
maximal independent set of `G - V₁`, `V₃` is a maximal independent set of
`G - (V₁ ∪ V₂)`, and so on.  It is easy to see (exercise 8.6.3) that if `G` is
`k`-colourable, then there exists a canonical `k`-colouring of `G`.  By repeatedly
using the above method for finding maximal independent sets, one can determine all
the canonical colourings of `G`.  The least number of colours used in such a
colouring is then the chromatic number of `G`.*

**Reading.**  Build the colour classes greedily, each time taking as large an
independent set as possible from what remains.  Exercise 8.6.3 shows this costs
nothing, so enumerating canonical colourings suffices to find `χ(G)` — the basis
of the §8.6 procedure for the storage problem, which the book concedes *is not
very efficient for large graphs*.

**Formalisation.**  Stated as a *static* condition on a list of classes, not as a
procedure: `L[i]` is required to be maximal-independent in the complement of
`L[0] ∪ … ∪ L[i-1]`, which is what "maximal independent set of
`G - (V₁ ∪ … ∪ V_{i-1})`" means.  The last two conjuncts say `L` really is a
partition — the classes cover `V` and are pairwise disjoint.  A `List` rather than
a `Fin k → Set V` because the book's condition is inherently ordered, and because
exercise 8.6.3 concludes with `L.length ≤ k` rather than `= k` (a canonical
colouring may use fewer colours, which is precisely why the procedure finds `χ`
rather than merely confirming `k`). -/
def IsCanonicalColouring {V : Type*} (G : SimpleGraph V) (L : List (Set V)) : Prop :=
  (∀ i (h : i < L.length),
      G.IsMaximalIndepSetIn (L.get ⟨i, h⟩) (Set.univ \ ⋃ j ∈ Finset.range i, L.getD j ∅)) ∧
  (⋃ s ∈ L, s) = Set.univ ∧ L.Pairwise Disjoint

/-- The Mycielski **tower** `G₂ = K₂, G₃, G₄, …`.

**Book context** (B&M exercise 8.5.1, verbatim).  *Let `G₃, G₄, …` be the graphs
obtained from `G₂ = K₂`, using Mycielski's construction.*

§8.5 adds: *By starting with the 2-chromatic graph `K₂`, the above construction
yields, for all `k ≥ 2`, a triangle-free `k`-chromatic graph on `3·2^{k-2} - 1`
vertices.*

**Reading.**  Iterate Mycielski's construction from a single edge.  The book
records the first few: `G₂ = K₂`, `G₃` is the 5-cycle, `G₄` is the Grötzsch graph
of figure 8.2.  Exercise 8.5.1 strengthens theorem 8.7 for this particular tower:
each `G_k` is not merely `k`-chromatic but `k`-*critical*.

**Formalisation.**  Each `G_k` lives on a different carrier (`V ⊕ V ⊕ Unit` of the
previous one), so the recursion must be `Sigma`-valued: it returns a carrier
*together with* a graph on it.  The book's tower starts at `k = 2`; the clauses
`0` and `1` are padding so the function is total, and every statement about the
tower carries the hypothesis `2 ≤ k`.  This def is the reason `mycielskian` must
exist as a standalone operation rather than being inlined into theorem 8.7. -/
def mycielskiTower : (k : ℕ) → Σ (V : Type), SimpleGraph V
  | 0 | 1 | 2 => ⟨Fin 2, ⊤⟩
  | (k + 1) => ⟨_, (mycielskiTower k).2.mycielskian⟩

/-!
## §8.1 — critical graphs, χ vs Δ

`Coloring`, `Colorable`, `chromaticNumber` are all Mathlib (`Coloring.lean`); `IsCritical` /
`IsKCritical` are the local anchors above.
-/

-- (8.0): every k-chromatic graph has a k-critical subgraph (B&M assert it with no proof)
/-- **Book assertion** (B&M §8.1, verbatim).  *A `k`-critical graph is one that is
`k`-chromatic and critical; every `k`-chromatic graph has a `k`-critical
subgraph.*

**Book proof.**  None — B&M assert this in passing, in the sentence that
introduces `k`-critical graphs, and never return to it.

**Skeleton** (for `∃ H : G.Subgraph, H.coe.IsKCritical k`).
1. Work with `S = {H : G.Subgraph | H.coe.chromaticNumber = k}`.  It is nonempty:
   `⊤ ∈ S`, since `(⊤ : G.Subgraph).coe ≃g G` and `hk` gives `χ(G) = k`.
2. `G.Subgraph` on a `Finite` carrier is itself finite (a subgraph is determined by
   `verts` and `Adj`), so the well-founded `<` on it lets us choose `H` **minimal**
   in `S`.  This is the step doing the book's "keep deleting as long as `χ` stays
   at `k`"; finiteness is what makes it terminate.
3. First half of `IsKCritical`: `H.coe.chromaticNumber = k` is just `H ∈ S`.
4. Second half: given `K : H.coe.Subgraph` with `K < ⊤`, transport `K` to a
   `G.Subgraph` `K'` with `K' < H` and `K'.coe ≃g K.coe` — subgraphs-of-a-subgraph
   correspond to subgraphs of `G` below `H`.
5. Minimality of `H` gives `K' ∉ S`, i.e. `χ(K'.coe) ≠ k`.  Monotonicity
   (`Colorable.mono` along the inclusion hom: a subgraph never needs more colours)
   gives `χ(K'.coe) ≤ χ(H.coe) = k`.  Together, `χ(K.coe) < k = χ(H.coe)`.

**Reading.**  Start with a `k`-chromatic graph and keep deleting vertices and edges
as long as the chromatic number stays at `k`.  The graph is finite, so this stops;
what remains is still `k`-chromatic but every proper subgraph of it needs fewer
colours — that is, it is `k`-critical.  This is the reduction that makes critical
graphs worth studying at all: any statement proved for `k`-critical graphs
transfers to all `k`-chromatic ones.  Corollary 8.1.1, Brooks' theorem 8.4 and
theorem 8.5 all open by invoking it.

**Formalisation.**  Only `[Finite V]` is needed, not `[Fintype V]`: the argument
uses finiteness solely to well-found the minimisation in step 2. -/
theorem exists_isKCritical_subgraph
    {V : Type*} [Finite V] {G : SimpleGraph V} {k : ℕ} (hk : G.chromaticNumber = k) :
    ∃ H : G.Subgraph, H.coe.IsKCritical k := by
  sorry

-- (8.0b): every critical graph is connected
/-- **Book remark** (B&M §8.1, verbatim).  *An easy consequence of the definition is
that every critical graph is connected.*

**Book proof.**  None — stated as an "easy consequence" and left to the reader.

**Skeleton** (for `G.Connected`).
1. `Connected` is `Preconnected ∧ Nonempty V`; the second conjunct is the
   `[Nonempty V]` instance, so only `Preconnected` is at issue.
2. `by_contra`: if `G` is not preconnected, there are at least two connected
   components — i.e. `c : G.ConnectedComponent` with `c.supp ≠ Set.univ`.
3. Key lemma, to be proved first: **`χ(G)` is attained by some component.**  No
   edge joins distinct components, so an independent choice of colouring per
   component assembles into a colouring of `G` (build the `Coloring` by
   `ConnectedComponent.lift`, checking properness edge-by-edge — both ends of an
   edge lie in the same component).  Hence
   `χ(G) = ⨆ c, χ((G.induce c.supp))`, and over a finite type the supremum is
   attained: fix `c₀` with `χ(G.induce c₀.supp) = χ(G)`.
4. Let `H : G.Subgraph` be the induced subgraph on `c₀.supp`.  Then `H < ⊤`,
   because step 2 supplies a vertex outside `c₀.supp`.
5. Criticality `h H (step 4)` gives `χ(H.coe) < χ(G)`, contradicting step 3.

**Reading.**  If a graph were disconnected, its chromatic number would be the
maximum of those of its components — colour each component independently.  So one
component already achieves `χ(G)`, and that component is a proper subgraph with
the same chromatic number, contradicting criticality.  Corollary 8.2 strengthens
this considerably: every critical graph is not merely connected but a *block*,
having no cut vertex at all.

**Formalisation.**  Step 3 is the whole content and is reusable: the same
"components colour independently" lemma is exercise 8.4.6 in its counting form
(`π_k` multiplies over components).  Worth proving once in a shared form. -/
theorem IsCritical.connected
    {V : Type*} [Finite V] [Nonempty V] {G : SimpleGraph V} (h : G.IsCritical) :
    G.Connected := by
  sorry

-- Thm 8.1: k-critical ⇒ δ ≥ k − 1  (the `k - 1` truncation is harmless as a lower bound)
/-- **Theorem 8.1.**  *If `G` is `k`-critical, then `δ ≥ k - 1`.*

**Book proof** (B&M §8.1, verbatim).  *By contradiction.  If possible, let `G` be a
`k`-critical graph with `δ < k - 1`, and let `v` be a vertex of degree `δ` in `G`.
Since `G` is `k`-critical, `G - v` is `(k-1)`-colourable.  Let
`(V₁, V₂, …, V_{k-1})` be a `(k-1)`-colouring of `G - v`.  By definition, `v` is
adjacent in `G` to `δ < k - 1` vertices, and therefore `v` must be nonadjacent in
`G` to every vertex of some `V_j`.  But then `(V₁, V₂, …, V_j ∪ {v}, …, V_{k-1})`
is a `(k-1)`-colouring of `G`, a contradiction.  Thus `δ ≥ k - 1`.*

**Skeleton** (for `k - 1 ≤ G.minDegree`).
1. `by_contra` and `push_neg`: assume `G.minDegree < k - 1`.  Obtain `v` with
   `G.degree v = G.minDegree` (`exists_minimal_degree_vertex`; `Nonempty V` follows
   from `h.1`, as an empty carrier forces `χ = 0 < k`).
2. Let `H : G.Subgraph` be the induced subgraph on `({v}ᶜ : Set V)` — the book's
   `G - v`.  Then `H < ⊤`, witnessed by `v ∉ H.verts`.
3. Criticality `h.2 H` with `h.1` gives `χ(H.coe) < k`, hence
   `H.coe.Colorable (k-1)`; obtain `c : H.coe.Coloring (Fin (k-1))`.
4. **The free colour.**  The image of `G.neighborFinset v` under `c` has card at
   most `G.degree v < k - 1 = |Fin (k-1)|`, so it is not everything: obtain
   `j : Fin (k-1)` with `∀ w ∈ G.neighborFinset v, c ⟨w, _⟩ ≠ j`.  This is the
   book's `V_j`, phrased as a pigeonhole rather than as a class that `v` misses.
5. Assemble `c' : G.Coloring (Fin (k-1))` sending `v ↦ j` and `w ↦ c ⟨w, _⟩`
   otherwise.  Properness splits into: edges avoiding `v`, where `c'` agrees with
   `c`; and edges at `v`, where step 4 applies.
6. `c'` gives `G.Colorable (k-1)`, so `χ(G) ≤ k - 1 < k`, contradicting `h.1`.

**Reading.**  A vertex of small degree is never an obstacle to colouring, since
some colour is always free for it.  So a graph that genuinely needs `k` colours,
*minimally*, cannot contain such a vertex — criticality is what turns "`v` is easy
to colour" into a contradiction rather than merely an observation.

**Formalisation.**  `k - 1` is ℕ-subtraction, but the statement is a lower bound,
so truncation is harmless: at `k = 0` it reads `0 ≤ minDegree`.  Step 4 is where
the strict inequality `δ < k - 1` is spent, so it needs `k ≥ 1` to know
`Fin (k-1)` is the right palette — available from `h.1` as in step 1. -/
theorem IsKCritical.minDegree_ge
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (h : G.IsKCritical k) :
    k - 1 ≤ G.minDegree := by
  sorry

-- Cor 8.1.1: every k-chromatic graph has ≥ k vertices of degree ≥ k − 1
/-- **Corollary 8.1.1.**  *Every `k`-chromatic graph has at least `k` vertices of
degree at least `k - 1`.*

**Book proof** (B&M §8.1, verbatim).  *Let `G` be a `k`-chromatic graph, and let `H`
be a `k`-critical subgraph of `G`.  By theorem 8.1, each vertex of `H` has degree
at least `k - 1` in `H`, and hence also in `G`.  The corollary now follows since
`H`, being `k`-chromatic, clearly has at least `k` vertices.*

**Skeleton** (for `k ≤ (univ.filter fun v => k - 1 ≤ G.degree v).card`).
1. `exists_isKCritical_subgraph hk` gives `H : G.Subgraph` with
   `H.coe.IsKCritical k`.
2. Theorem 8.1 applied to `H.coe`: `k - 1 ≤ H.coe.minDegree`, so every
   `w : H.verts` has `k - 1 ≤ H.coe.degree w`.
3. **Degree monotonicity**, the book's "and hence also in `G`":
   `H.coe.degree w ≤ G.degree w.val`, since `H`'s neighbourhood of `w` injects
   into `G`'s.  So `H.verts.toFinset ⊆ univ.filter fun v => k - 1 ≤ G.degree v`.
4. **`k ≤ |H.verts|`**, the book's "clearly has at least `k` vertices": a graph on
   `n` vertices is `n`-colourable, so `χ ≤ card`; with `χ(H.coe) = k` this gives
   `k ≤ |H.verts|`.
5. Chain 4 and 3 through `Finset.card_le_card`.

**Reading.**  Needing `k` colours is not a global accident — it forces `k` distinct
vertices each locally rich enough (degree `≥ k - 1`) to be part of the obstruction.
The critical subgraph is what localises the difficulty; without it, "`G` needs `k`
colours" says nothing about any individual vertex.

**Formalisation.**  Step 3 is stated about `G.degree`, not `H.coe.degree`, which is
why the filter in the goal mentions only `G` — the critical subgraph is existential
and does not appear in the statement. -/
theorem card_filter_degree_ge_of_chromaticNumber
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (hk : G.chromaticNumber = k) :
    k ≤ (Finset.univ.filter fun v => k - 1 ≤ G.degree v).card := by
  sorry

-- Cor 8.1.2: χ ≤ Δ + 1  (cheapest win; prove directly, NOT via B&M's Cor-8.1.1 route)
/-- **Corollary 8.1.2.**  *For any graph `G`, `χ ≤ Δ + 1`.*

**Book proof** (B&M §8.1, verbatim).  *This is an immediate consequence of corollary
8.1.1.*

**Skeleton.**  Two routes; the second is the one to fill.

*The book's route* (via corollary 8.1.1, unpacking "immediate").
1. `by_contra`: assume `Δ + 1 < χ(G)`.  With `χ(G)` finite (carrier is a
   `Fintype`), set `k = χ(G)`, so `k ≥ Δ + 2`.
2. Corollary 8.1.1 supplies `k` vertices of degree `≥ k - 1 ≥ Δ + 1`.
3. But `G.degree v ≤ G.maxDegree = Δ` for every `v` (`degree_le_maxDegree`), and
   step 2 needs at least one such vertex — contradiction.

*The direct route* (independent of 8.0/8.1, and cheaper here — prefer it).
1. Check first whether Mathlib already has this
   (`chromaticNumber_le_maxDegree_add_one` or similar) via `exact?`.
2. Otherwise, strong induction on `Fintype.card V`.  Pick any `v`; the induced
   subgraph on `({v}ᶜ : Set V)` has `maxDegree ≤ G.maxDegree`, so the induction
   hypothesis gives it a `(Δ+1)`-colouring `c`.
3. `|c '' N(v)| ≤ G.degree v ≤ Δ < Δ + 1`, so some colour `j` is free at `v`.
4. Extend `c` by `v ↦ j` and check properness — steps 4–6 of theorem 8.1, with
   the palette `Fin (Δ+1)` in place of `Fin (k-1)`.

**Reading.**  Colour the vertices one at a time in any order: when a vertex's turn
comes it has at most `Δ` neighbours, so at most `Δ` colours are forbidden and one
of `Δ + 1` is always free.  The book observes the bound *is sometimes very much
greater than the actual value* — bipartite graphs are 2-chromatic with arbitrarily
large `Δ` — making it weaker than Vizing's edge analogue (theorem 6.2) in one
sense; and weaker in a second sense too, since *many* graphs satisfy `χ' = Δ + 1`
whereas Brooks' theorem 8.4 shows only two families satisfy `χ = Δ + 1`.

**Formalisation.**  The book's route is recorded because it is the book's, but the
direct route is preferred: it avoids depending on `exists_isKCritical_subgraph`
and `IsKCritical.minDegree_ge`, both of which are substantially harder than this
corollary.  This is the cheapest genuine win in the file — a good first fill. -/
theorem chromaticNumber_le_maxDegree_add_one
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.chromaticNumber ≤ G.maxDegree + 1 := by
  sorry

-- Thm 8.2: in a critical graph, no vertex cut is a clique  (`hconn` is load-bearing — Warning 6)
/-- **Theorem 8.2.**  *In a critical graph, no vertex cut is a clique.*

**Book proof** (B&M §8.1, verbatim).  *By contradiction.  Let `G` be a `k`-critical
graph, and suppose that `G` has a vertex cut `S` that is a clique.  Denote the
`S`-components of `G` by `G₁, G₂, …, G_n`.  Since `G` is `k`-critical, each `Gᵢ`
is `(k-1)`-colourable.  Furthermore, because `S` is a clique, the vertices in `S`
must receive distinct colours in any `(k-1)`-colouring of `Gᵢ`.  It follows that
there are `(k-1)`-colourings of `G₁, G₂, …, G_n` which agree on `S`.  But these
colourings together yield a `(k-1)`-colouring of `G`, a contradiction.*

**Skeleton** (for `¬ G.IsClique (S : Set V)`).
1. `intro hclique`.  Extract `k := χ(G)` from `hcrit`; note `k ≥ 1`.
2. **The pieces.**  For each `c : (G.induce (↑S)ᶜ).ConnectedComponent`, let
   `Gc : G.Subgraph` be the induced subgraph on `Subtype.val '' c.supp ∪ ↑S` (the
   `S`-component; `uvComponent` is the two-element case of this).  Each `Gc < ⊤`,
   because `hS` supplies a second component whose vertices are missing — **this is
   where `hS` being a genuine cut is used**, and where `hconn` enters (see below).
3. Criticality gives `Gc.coe.Colorable (k-1)` for every `c`; pick `cc` for each.
4. **Rigidity of a clique.**  `hclique` forces `cc` to be injective on `↑S`.  Hence
   for any two components `c, c'` there is a permutation `σ : Equiv.Perm (Fin (k-1))`
   with `σ ∘ cc' = cc` on `S`: two injections from a finite set into `Fin (k-1)`
   differ by a permutation.  Normalise every `cc` this way against a fixed
   reference component, so all of them **agree on `S`**.
5. **Gluing.**  Define `c* : G.Coloring (Fin (k-1))` by sending `v ∈ ↑S` to its
   common colour and `v ∉ ↑S` to `cc v` for `c` the component of `v`.  Properness:
   every edge of `G` lies inside some `Gc` — an edge with both ends outside `S`
   cannot cross components, and an edge meeting `S` lies in the component of its
   other end — so it is properly coloured by that `cc`, hence by `c*`.
6. `χ(G) ≤ k - 1 < k`, contradiction.

**Reading.**  A clique cut is too rigid to cause trouble: its vertices are forced
to take distinct colours anyway, and distinct colours can always be permuted into
agreement, so the pieces reconcile and the graph never needed the extra colour.
Step 4 is the entire content — for a general cut the restrictions to `S` need not
be related by a permutation, and exercise 8.1.8 identifies the exact weakening
(uniquely `(k-1)`-colourable) under which the argument still runs.

**Formalisation.**  `hconn : G.Connected` is load-bearing and is *not* redundant
given `hcrit`: although `IsCritical.connected` proves connectivity from
criticality, it needs `[Nonempty V]`, which this statement does not assume.
Passing `hconn` explicitly keeps the two results independent and avoids a
dependency cycle.  Note also that the book's `S`-components are defined only for a
*connected* `G`, so step 2 genuinely needs it. -/
theorem IsCritical.not_isClique_of_isVertexCut
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hcrit : G.IsCritical) (hconn : G.Connected)
    {S : Finset V} (hS : G.IsVertexCut S) :
    ¬ G.IsClique (S : Set V) := by
  sorry

-- Cor 8.2: every critical graph is a block  (no `IsBlock` def — "block" unfolds to no-cut-vertex)
/-- **Corollary 8.2.**  *Every critical graph is a block.*

**Book proof** (B&M §8.1, verbatim).  *If `v` is a cut vertex, then `{v}` is a vertex
cut which is also, trivially, a clique.  It follows from theorem 8.2 that no
critical graph has a cut vertex; equivalently, every critical graph is a block.*

The term is B&M §3.1: *A connected graph that has no cut vertices is called a
block.*

**Skeleton** (for `G.Connected ∧ ∀ v, ¬ G.IsVertexCut {v}`).
1. **Left conjunct.**  `IsCritical.connected hcrit` — this is where `[Nonempty V]`
   is needed.
2. **Right conjunct.**  `intro v hv`, so `hv : G.IsVertexCut {v}`.
3. `({v} : Set V)` is a clique: `IsClique` on a singleton is vacuous
   (`Set.Subsingleton.isClique`).  This is the book's "trivially, a clique".
4. `hcrit.not_isClique_of_isVertexCut (step 1) hv` contradicts step 3.

**Reading.**  Criticality forces the graph to hold together tightly: it can have no
single point of failure.  Theorem 8.3 goes one step further and analyses the
2-vertex cuts that remain possible — and finds they too are heavily constrained.

**Formalisation.**  There is no `IsBlock` in Mathlib or this repo, so "is a block"
is unfolded into the book's own definition, connected + no cut vertex.  A cut
vertex is spelled as a one-element vertex cut, matching `IsVertexCut` above.  The
`Connected` conjunct is not merely decoration: without it the statement would be
satisfied by the empty graph. -/
theorem IsCritical.connected_and_no_cut_vertex
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {G : SimpleGraph V}
    (hcrit : G.IsCritical) :
    G.Connected ∧ ∀ v : V, ¬ G.IsVertexCut ({v} : Finset V) := by
  sorry

-- (8.2a): a 2-vertex cut of a k-critical graph is non-adjacent
/-- **Book consequence of theorem 8.2** (B&M §8.1, verbatim).  *Another consequence of
theorem 8.2 is that if a `k`-critical graph `G` has a 2-vertex cut `{u, v}`, then
`u` and `v` cannot be adjacent.*

**Book proof.**  None — B&M state it as an immediate consequence, in the sentence
that then introduces the type 1 / type 2 dichotomy.

**Skeleton** (for `¬ G.Adj u v`).
1. `intro hadj`.
2. `({u, v} : Set V)` is a clique: the only pair to check is `u`, `v` themselves
   (`huv : u ≠ v` rules out the diagonal), and `hadj` supplies the edge.  Mathlib:
   `isClique_pair` / `IsClique` unfolded on `Set.pair`.
3. `G.Connected` from `IsCritical.connected hcrit`.
4. `hcrit.not_isClique_of_isVertexCut (step 3) hS` contradicts step 2 — noting
   `↑({u,v} : Finset V) = ({u,v} : Set V)` so the coercions line up.

**Reading.**  This is what makes the type 1 / type 2 dichotomy meaningful.  Since
`u` and `v` are *not* joined by an edge, a `(k-1)`-colouring of a
`{u,v}`-component is free to give them the same colour or different colours; which
it is *forced* to do is exactly the component's type.  Were `uv` an edge, every
component would be trivially of type 2 and theorem 8.3 would say nothing.

**Formalisation.**  Stated for `IsCritical` rather than `IsKCritical`: the book
says "`k`-critical", but `k` plays no role in the argument, so the hypothesis is
weakened to plain criticality.  `huv : u ≠ v` is needed to know `{u, v}` really has
two elements. -/
theorem IsCritical.not_adj_of_isVertexCut_pair
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {G : SimpleGraph V}
    (hcrit : G.IsCritical) {u v : V} (huv : u ≠ v)
    (hS : G.IsVertexCut ({u, v} : Finset V)) :
    ¬ G.Adj u v := by
  sorry

-- Ex 8.1.1: χ ≥ ν²/(ν² − 2ε), restated multiplicatively over ℝ
/-- **Exercise 8.1.1** (B&M §8.1, verbatim).  *Show that if `G` is simple, then
`χ ≥ ν²/(ν² - 2ε)`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `ν² ≤ k * (ν² - 2ε)` over `ℝ`, given `hk : G.Colorable k`).
1. Obtain `c : G.Coloring (Fin k)` from `hk`, and set
   `n i = (c.colorClass i).toFinset.card` for `i : Fin k`.  The colour classes
   partition `V`, so `∑ i, n i = ν`.
2. **Edges avoid classes.**  Count ordered pairs: `∑ i, (n i)^2` is the number of
   ordered pairs `(x, y)` with `c x = c y`, and every edge `s(x,y)` contributes two
   ordered pairs with `c x ≠ c y` (properness).  Hence `2ε ≤ ν² - ∑ i, (n i)^2`,
   i.e. `∑ i, (n i)^2 ≤ ν² - 2ε`.
3. **Cauchy–Schwarz** in the form `(∑ i, n i)^2 ≤ k * ∑ i, (n i)^2`
   (`Finset.sq_sum_le_card_mul_sum_sq`, or `inner_mul_le_norm_mul_norm`).  With
   step 1 this is `ν² ≤ k * ∑ i, (n i)^2`.
4. Chain 3 and 2: `ν² ≤ k * ∑ (n i)^2 ≤ k * (ν² - 2ε)`, which is the goal.  The
   second inequality needs `0 ≤ k`, which is free.

**Reading.**  Many edges force many colours: each colour class is edge-free, so
large classes leave too little room for edges.  Equality holds exactly for
balanced complete multipartite graphs, where every non-edge is inside a class and
all classes have the same size.

**Formalisation.**  Stated multiplicatively over `ℝ` — `ν²/(ν² - 2ε)` would need
division and a proof that the denominator is nonzero.  (It always is: `G` simple
gives `2ε ≤ ν(ν-1) < ν²`, so `ν² - 2ε ≥ ν > 0` whenever `V` is nonempty, whence
the `[Nonempty V]` hypothesis.)  `χ` is replaced by an arbitrary `k` with
`G.Colorable k`, dodging `ℕ∞`; this is equivalent to the book's statement, since
the right-hand side is monotone in `k` and `χ` is the least colourable `k`. -/
theorem chromaticNumber_ge_of_card_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] {k : ℕ} (hk : G.Colorable k) :
    ((Fintype.card V : ℝ))^2 ≤ (k : ℝ) * ((Fintype.card V : ℝ)^2 - 2 * G.edgeFinset.card) := by
  sorry

-- Ex 8.1.2: if any two odd cycles of G meet, then χ ≤ 5
/-- **Exercise 8.1.2** (B&M §8.1, verbatim).  *Show that if any two odd cycles of `G`
have a vertex in common, then `χ ≤ 5`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `G.chromaticNumber ≤ 5`).
0. First prove the reusable splitting lemma
   `χ(G) ≤ χ(G.induce A) + χ(G.induce Aᶜ)`: colour the two sides with disjoint
   palettes (`Sum` of the two colour types) and check properness edge-by-edge —
   an edge either stays within a side or is coloured by distinct palettes.
1. **Case: `G` has no odd cycle.**  Then `G` is bipartite (theorem 1.2), so
   `χ ≤ 2 ≤ 5` and we are done.
2. **Otherwise** choose an odd cycle of *minimum length* and let `C : Set V` be
   its support.
3. **`G.induce C` is exactly that cycle.**  A chord would split it into two cycles
   whose lengths sum to `|C| + 2`; one of them is odd and shorter, contradicting
   minimality.  Hence `χ(G.induce C) ≤ 3` (an odd cycle is 3-colourable).
4. **`G.induce Cᶜ` is bipartite.**  An odd cycle inside it would be vertex-disjoint
   from the cycle of step 2, contradicting `h`.  Hence `χ(G.induce Cᶜ) ≤ 2`.
5. Step 0 with `A = C`, then steps 3 and 4: `χ(G) ≤ 3 + 2 = 5`.

**Reading.**  Odd cycles are the sole obstruction to 2-colourability, so if they
all pile up on one shortest cycle, only a bounded amount of extra colour is needed
to handle them.  Minimality in step 2 is what makes the cycle *induced*, and hence
3-colourable rather than merely small.

**Formalisation.**  The hypothesis quantifies over all pairs of closed walks that
are cycles of odd length, and asks for a common *support* vertex.  Note `h` is
also applied with `p = q` in step 2's minimality argument, where it is vacuous —
the content is only in the disjointness contradiction of step 4. -/
theorem chromaticNumber_le_five_of_odd_cycles_meet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h : ∀ (u w : V) (p : G.Walk u u) (q : G.Walk w w), p.IsCycle → q.IsCycle →
          Odd p.length → Odd q.length → ∃ x, x ∈ p.support ∧ x ∈ q.support) :
    G.chromaticNumber ≤ 5 := by
  sorry

-- Ex 8.1.3 (Welsh–Powell): χ ≤ maxᵢ min{dᵢ+1, i}  (degree sequence as a degree-antitone Equiv)
/-- **Exercise 8.1.3** (B&M §8.1, verbatim; Welsh and Powell).  *Show that if `G` has
degree sequence `(d₁, d₂, …, d_ν)` with `d₁ ≥ d₂ ≥ … ≥ d_ν`, then
`χ ≤ maxᵢ min{dᵢ + 1, i}`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `χ(G) ≤ univ.sup fun i => min (G.degree (σ i) + 1) (i + 1)`).
1. **The greedy colouring.**  Define `f : Fin (card V) → ℕ` by strong recursion on
   `i`: `f i` is the least natural not in
   `{f j | j < i ∧ G.Adj (σ j) (σ i)}` (`Nat.find` over a finite blocked set).
2. **Properness.**  For adjacent `σ i`, `σ j` with `i ≠ j`, say `j < i`: then
   `f j` is in the blocked set at step `i`, so `f i ≠ f j`.
3. **The two bounds at each step** — the heart, and independent of `hσ`:
   * `f i ≤ i`, since at most `i` earlier indices block a colour;
   * `f i ≤ G.degree (σ i)`, since at most that many neighbours block one.
   Together `f i < min (G.degree (σ i) + 1) (i + 1)`.
4. Hence `f i < M` for `M := univ.sup fun i => min (G.degree (σ i) + 1) (i + 1)`,
   so `f` corestricts to `Fin M`, giving `G.Colorable M` via `σ` and step 2, and
   therefore `χ(G) ≤ M`.

**Reading.**  Colour greedily in order of decreasing degree.  When the `i`-th
vertex's turn comes, two things bound the colours forbidden to it: it has `dᵢ`
neighbours, so at most `dᵢ` colours are blocked; and only `i - 1` vertices are
coloured so far, so at most `i - 1` colours exist.  Hence `min{dᵢ + 1, i}` colours
suffice at step `i`, and the worst case over `i` bounds `χ`.  This genuinely
improves `χ ≤ Δ + 1` (corollary 8.1.2): high-degree vertices are handled while few
colours exist, low-degree ones later when the count `i` no longer binds.
Exercise 8.1.4 derives two further bounds from it.

**Formalisation.**  The sorted degree sequence is presented as an equivalence
`σ : Fin (card V) ≃ V` together with `hσ`, which says `i ↦ deg (σ i)` is antitone —
i.e. `σ` enumerates the vertices in nonincreasing degree order, so
`G.degree (σ i)` *is* the book's `dᵢ`.  `i + 1` rather than `i` because `Fin` is
0-indexed and the book is 1-indexed.

Worth knowing while filling: **`hσ` is not needed for the proof**, only for the
statement.  Steps 1–4 bound `χ` by that `sup` for *any* enumeration `σ`; what `hσ`
buys is that the `sup` is then the book's `maxᵢ min{dᵢ + 1, i}` for the sorted
sequence, which is the small quantity worth having.  So do not go looking for a
place to use `hσ` — there isn't one. -/
theorem welsh_powell {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Fin (Fintype.card V) ≃ V) (hσ : Antitone fun i => G.degree (σ i)) :
    G.chromaticNumber ≤ (Finset.univ.sup fun i : Fin (Fintype.card V) =>
      min (G.degree (σ i) + 1) (i + 1)) := by
  sorry

-- Ex 8.1.4(a): χ ≤ ⌈√(2ε)⌉  ({x} is the CEILING)
/-- **Exercise 8.1.4(a)** (B&M §8.1, verbatim).  *Using exercise 8.1.3, show that
`χ ≤ {(2ε)^{1/2}}`.*

**Book proof.**  None — an exercise.

**⚠ Statement repaired — deviates from the book.**  The book's statement is **false**
as written, and a naive transcription would be too.  Take `G = ⊥` on a one-vertex
carrier: `χ = 1` but `ε = 0`, so `⌈√(2ε)⌉ = 0` and the claim reads `1 ≤ 0`.  More
generally the edgeless graph on any nonempty carrier is a counterexample, and it is
the only one — the argument below goes through as soon as `G` has an edge.  The
hypothesis `he : 1 ≤ G.edgeFinset.card` has therefore been **added** to the
signature; `G ≠ ⊥` would serve equally well.  This is a deliberate divergence from
B&M, recorded here so it is not mistaken for a transcription slip.

**Skeleton** (for `χ(G) ≤ ⌈√(2ε)⌉`, given `he`).
1. Set `k = χ(G)` (finite, as `V` is a `Fintype`).
2. **`k(k-1) ≤ 2ε`.**  Corollary 8.1.1 gives `k` vertices of degree at least
   `k - 1`; summing over just those, `k(k-1) ≤ ∑ v, G.degree v`, and the handshake
   lemma (`sum_degrees_eq_twice_card_edges`) turns the right side into `2ε`.
   (This is the book's "using exercise 8.1.3" step done via 8.1.1 instead — 8.1.3
   would reach the same inequality but through the sorted degree sequence, which
   is more work here.)
3. **From `k(k-1) ≤ 2ε` to the goal.**  Put `m = ⌈√(2ε)⌉` and argue by
   contradiction: if `m + 1 ≤ k` then `m(m+1) ≤ k(k-1) ≤ 2ε`, while `m ≥ √(2ε)`
   gives `2ε ≤ m²`.  Hence `m² + m ≤ m²`, so `m = 0`, so `ε = 0` — excluded by the
   the hypothesis `he`.  This is exactly the point where `1 ≤ ε` is spent.
4. Cast back to `ℕ∞` for the `chromaticNumber` goal.

**Reading.**  Needing many colours forces many edges: a `χ`-chromatic graph carries
at least as many edges as `K_χ`.  So a sparse graph cannot have a large chromatic
number.

**Formalisation.**  The book's `{x}` denotes the **ceiling**, rendered as `⌈·⌉₊`
(`Nat.ceil`), which is the correct choice here since the quantity is nonnegative.
`Real.sqrt` needs a real argument, hence the cast on `2 * ε`. -/
theorem chromaticNumber_le_ceil_sqrt_two_mul_card_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (he : 1 ≤ G.edgeFinset.card) :
    G.chromaticNumber ≤ ⌈Real.sqrt (2 * G.edgeFinset.card)⌉₊ := by
  sorry

-- Ex 8.1.4(b) (Nordhaus–Gaddum): χ(G) + χ(Gᶜ) ≤ ν + 1
/-- **Exercise 8.1.4(b)** (B&M §8.1, verbatim; Nordhaus and Gaddum).  *Using exercise
8.1.3, show that `χ(G) + χ(Gᶜ) ≤ ν + 1`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `χ(G) + χ(Gᶜ) ≤ ν + 1` in `ℕ∞`).
1. Both chromatic numbers are finite; extract `a = χ(G)`, `b = χ(Gᶜ)` in `ℕ` and
   reduce the goal to `a + b ≤ ν + 1` in `ℕ`.
2. **Key consequence of 8.1.3**, to be proved as a standalone `have`: writing
   `d₁ ≥ … ≥ d_ν` for `G`'s sorted degree sequence, `χ(G) = a` implies
   `d_a ≥ a - 1`.  *Why:* exercise 8.1.3 gives `a ≤ maxᵢ min{dᵢ + 1, i}`, so some
   `i` has `a ≤ i` and `a ≤ dᵢ + 1`; since the sequence is nonincreasing and
   `a ≤ i`, `d_a ≥ dᵢ ≥ a - 1`.  (Equivalently: corollary 8.1.1.)
3. Apply step 2 to `Gᶜ`.  Its degrees are `d_{Gᶜ}(v) = ν - 1 - d_G(v)`, so `Gᶜ`'s
   *decreasing* sequence is `ν - 1 - d_{ν+1-j}` — reversal plus complement.  Step 2
   for `Gᶜ` therefore reads `ν - 1 - d_{ν+1-b} ≥ b - 1`, i.e.
   `d_{ν+1-b} ≤ ν - b`.
4. **Contradiction.**  Suppose `a + b ≥ ν + 2`.  Then `ν + 1 - b ≤ a - 1`, so by
   monotonicity `d_{ν+1-b} ≥ d_a ≥ a - 1` (step 2).  But `a + b ≥ ν + 2` also gives
   `ν - b ≤ a - 2`, so step 3 gives `d_{ν+1-b} ≤ a - 2`.  Hence `a - 1 ≤ a - 2`,
   absurd.

**Reading.**  A graph and its complement cannot both be hard to colour: an edge
missing from `G` is present in `Gᶜ`, so the two compete for the same `ν - 1`
adjacencies at each vertex.  Equality holds for complete graphs, where
`χ(Kₙ) = n` and `χ(Kₙᶜ) = 1`.  This is the archetypal Nordhaus–Gaddum inequality,
of which many analogues are known for other graph parameters.

**Formalisation.**  The addition is in `ℕ∞`, where subtraction is badly behaved —
hence step 1, which moves the whole argument into `ℕ` before any arithmetic.  Step
3's index gymnastics (reverse, then complement) is the fiddliest part and is worth
isolating as its own lemma about the two sorted sequences. -/
theorem nordhaus_gaddum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.chromaticNumber + Gᶜ.chromaticNumber ≤ (Fintype.card V : ℕ∞) + 1 := by
  sorry

-- Ex 8.1.5 (Szekeres–Wilf): χ ≤ 1 + max over induced subgraphs of δ
/-- **Exercise 8.1.5** (B&M §8.1, verbatim; Szekeres and Wilf).  *Show that
`χ(G) ≤ 1 + max δ(H)`, where the maximum is taken over all induced subgraphs `H`
of `G`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `χ(G) ≤ 1 + univ.sup fun s : Finset V => (G.induce ↑s).minDegree`).
1. Abbreviate `D` for that `sup`.  Unfolding the `sup`: **every** induced subgraph
   `G.induce ↑s` has `minDegree ≤ D`, so every *nonempty* `s` contains a vertex `v`
   with `(G.induce ↑s).degree v ≤ D`.  This is the only property of `D` used.
2. **Generalise before inducting.**  Prove `∀ s : Finset V, (G.induce ↑s).Colorable (D + 1)`
   by strong induction on `s.card`; the theorem is the case `s = univ`.  (Inducting
   on `V` directly does not work — the induction hypothesis must apply to induced
   subgraphs of the *same* `G`, so that `D` stays fixed.)
3. **Base.**  `s = ∅`: the empty graph is colourable with any palette.
4. **Step.**  For `s` nonempty, step 1 gives `v ∈ s` of degree `≤ D` within `s`.
   Apply the induction hypothesis to `s.erase v` for a colouring `c`.
5. `v` has at most `D` neighbours inside `s`, so at most `D` of the `D + 1` colours
   are blocked; pick a free `j` and extend `c` by `v ↦ j`, checking properness as
   in theorem 8.1 step 5.

**Reading.**  `D` is the **degeneracy** of `G`.  Strip off a vertex of degree at
most `D`, repeatedly, recording the order; then colour the vertices back in reverse
order — when a vertex is restored it has at most `D` neighbours already present, so
one of `D + 1` colours is free.  This refines `χ ≤ Δ + 1` (corollary 8.1.2), since
`D ≤ Δ` always and often `D` is far smaller: a tree has `D = 1`, giving `χ ≤ 2` no
matter how large `Δ` is.

**Formalisation.**  "Induced subgraph" is indexed by `Finset V` (a vertex subset)
rather than by a `Subgraph`, since the book's maximum is over *induced* subgraphs
only.  The `sup` includes `s = ∅`, whose `minDegree` is `0` by Mathlib's
convention; this can only make `D` larger and so weakens the bound harmlessly.
Note the induction in step 2 is the formal content of "repeatedly strip off" — as
usual, the informal repetition becomes an induction on the size of what remains. -/
theorem szekeres_wilf {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    G.chromaticNumber ≤ 1 + (Finset.univ.sup fun s : Finset V =>
      (G.induce (s : Set V)).minDegree) := by
  sorry

-- Ex 8.1.6* (Gallai): if some colouring has every colour class of size ≥ 2, so does a χ-colouring
/-- **Exercise 8.1.6*** (B&M §8.1, verbatim; T. Gallai).  *If a `k`-chromatic graph
`G` has a colouring in which each colour is assigned to at least two vertices,
show that `G` has a `k`-colouring of this type.*

**Book proof.**  None — an exercise, and one the book **stars** as difficult.

**Skeleton** (for `∃ C : G.Coloring (Fin k), ∀ i, 2 ≤ (C.colorClass i).ncard`).
The natural shape is a downward induction on the number of colours, preserving the
"no singleton class" invariant.
1. Strengthen to: *if `G` has an `n`-colouring with every class of size `≥ 2` and
   `k < n`, then it has an `(n-1)`-colouring with every class of size `≥ 2`.*
   Iterating from the given `n` down to `k` proves the theorem; the induction is on
   `n - k`.
2. Inside the step, fix such an `n`-colouring `c` with `n > k = χ(G)`.  Since `n`
   exceeds the chromatic number, `c` is not optimal, and the goal is to eliminate
   one colour without creating a singleton.
3. Useful `have`, needed repeatedly: if a class `c⁻¹ i` is a singleton `{v}` in
   *some* `k`-colouring, then `v` has a neighbour in **every** other class —
   otherwise recolour `v` into that class and obtain a `(k-1)`-colouring,
   contradicting `hk`.
4. The exchange move: pick `u` in the same class as `v` under the *given* colouring
   from `h` (so `u ≠ v` and `¬ G.Adj u v`), and move `u` into `v`'s class.  Both
   classes stay independent.  Three cases on `|c⁻¹ (c u)|`:
   * `= 1`: then `{u}` and `{v}` are nonadjacent singleton classes; merge them for
     a colouring with one colour fewer — the step's goal.
   * `≥ 3`: the move strictly decreases the number of singleton classes.
   * `= 2`: **the hard case** — the move merely trades one singleton for another,
     so a naive "minimise the singleton count" potential stalls here.  This is
     where the star sits; a correct fill needs a genuinely global argument (a
     stronger potential, or an alternating-path/exchange argument across several
     classes at once), not a further local swap.

**Reading.**  The hypothesis provides *some* colouring, possibly using far more
than `k` colours, in which no colour class is a singleton.  The claim is that this
feature survives optimisation down to `k` colours.  The difficulty is that the two
requirements pull against each other: merging classes reduces the colour count but
tends to empty classes out, and the whole point is that it can be arranged never to
leave one vertex stranded.

**Formalisation.**  The hypothesis is existential in the number of colours `n`, so
the given colouring is `C : G.Coloring (Fin n)` for an unknown `n` — step 1's
strengthening is what makes that usable.  `Set.ncard` is used rather than a
`Finset` card so the statement needs no decidability on colour classes. -/
theorem gallai_two_per_class {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {k : ℕ} (hk : G.chromaticNumber = k)
    (h : ∃ (n : ℕ) (C : G.Coloring (Fin n)), ∀ i : Fin n, 2 ≤ (C.colorClass i).ncard) :
    ∃ C : G.Coloring (Fin k), ∀ i : Fin k, 2 ≤ (C.colorClass i).ncard := by
  sorry

-- Ex 8.1.7: the only 3-critical graphs are the odd cycles (up to iso).  Brooks consumes this.
/-- **Exercise 8.1.7**, third case (B&M §8.1, verbatim).  *Show that the only
1-critical graph is `K₁`, the only 2-critical graph is `K₂`, and the only
3-critical graphs are the odd `k`-cycles with `k ≥ 3`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `G.IsKCritical 3 ↔ ∃ n, Odd n ∧ 3 ≤ n ∧ Nonempty (G ≃g cycleGraph n)`).

*(←) an odd cycle is 3-critical.*
1. `χ(cycleGraph n) = 3` for odd `n ≥ 3`: it is 3-colourable, and not 2-colourable
   since an odd cycle is not bipartite (theorem 1.2).  Check
   `Mathlib.Combinatorics.SimpleGraph.ConcreteColorings` first — much of this is
   already there.
2. Criticality: a proper subgraph of a cycle misses a vertex or an edge, and in
   either case is a disjoint union of paths, hence bipartite, hence `χ ≤ 2 < 3`.

*(→) a 3-critical graph is an odd cycle.*  The efficient route is **not** via
degrees but via the "criticality forces the witness to be everything" pattern:
3. `χ(G) = 3` means `G` is not bipartite, so `G` contains an odd cycle `c`
   (theorem 1.2 again, in its contrapositive form).
4. Let `H : G.Subgraph` be the subgraph carried by that cycle — support and edges.
   By step 1, `χ(H.coe) = 3 = χ(G)`.
5. Criticality then **forbids** `H < ⊤`, so `H = ⊤`: `G` *is* the cycle.  Read off
   `n` as its length, odd by step 3 and `≥ 3` since `G` is simple.

**Reading.**  An odd cycle is 3-chromatic and minimally so — delete any edge or
vertex and it unrolls into a path, which is 2-colourable.  Conversely a 3-critical
graph cannot contain an odd cycle properly, and it must contain one, so it *is*
one.  This classification is exactly what Brooks' theorem 8.4 consumes: its proof
observes that *since 1-critical and 2-critical graphs are complete and 3-critical
graphs are odd cycles, we have `k ≥ 4`*.

**Formalisation.**  "The only 3-critical graphs are the odd cycles" is up to
isomorphism, hence `Nonempty (G ≃g cycleGraph n)` rather than an equality.  Steps
3–5 are the same three moves used in `isKCritical_two_iff` (with an edge in place
of an odd cycle); factoring out "a subgraph attaining `χ(G)` must be `⊤`" as a
lemma about `IsCritical` pays for itself across all three cases of 8.1.7. -/
theorem isKCritical_three_iff_odd_cycle {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} :
    G.IsKCritical 3 ↔ ∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ Nonempty (G ≃g cycleGraph n) := by
  sorry

-- Ex 8.1.7 (cont.): the only 1-critical graph is K₁, the only 2-critical graph is K₂ (up to iso)
/-- **Exercise 8.1.7**, first case (B&M §8.1, verbatim).  *Show that the only
1-critical graph is `K₁` …*

**Book proof.**  None — an exercise.

**Skeleton** (for `G.IsKCritical 1 ↔ Nonempty (G ≃g (⊤ : SimpleGraph (Fin 1)))`).

*(→).*
1. `χ(G) = 1` forces `G = ⊥`: a graph is 1-colourable exactly when it is edgeless
   (the book's remark in §8.1), and `χ ≥ 1` needs `V` nonempty.
2. Suppose `2 ≤ card V`.  Let `H : G.Subgraph` be the subgraph induced on a single
   vertex.  Then `H < ⊤`, but `χ(H.coe) = 1` — not `< 1`.  This contradicts
   criticality, so `card V = 1`.
3. On a one-element carrier `⊥ = ⊤`, so `G ≃g (⊤ : SimpleGraph (Fin 1))` via the
   unique bijection.

*(←).*  `K₁` is 1-chromatic, and its only proper subgraph is the empty one, with
`χ = 0 < 1`.

**Reading.**  A 1-chromatic graph has no edges and at least one vertex.
Criticality forces exactly one — with two or more vertices, deleting one leaves a
graph still needing one colour, so the chromatic number would not drop.

**Formalisation.**  `⊤ : SimpleGraph (Fin 1)` is `K₁`; on a single vertex the
complete and empty graphs coincide, which is what makes step 3 go through despite
`G` being edgeless.  Note that without the `Subgraph`-lattice definition of
`IsCritical`, step 2 would fail: the edge-only order has no proper subgraph of `⊥`
to test, and every edgeless graph would count as 1-critical. -/
theorem isKCritical_one_iff {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} :
    G.IsKCritical 1 ↔ Nonempty (G ≃g (⊤ : SimpleGraph (Fin 1))) := by
  sorry

/-- **Exercise 8.1.7**, second case (B&M §8.1, verbatim).  *… the only 2-critical
graph is `K₂` …*

**Book proof.**  None — an exercise.

**Skeleton** (for `G.IsKCritical 2 ↔ Nonempty (G ≃g (⊤ : SimpleGraph (Fin 2)))`).

*(→).*  The same three moves as the 3-critical case, with an edge in place of an
odd cycle:
1. `χ(G) = 2` forces `G` to have an edge `u ~ v` — otherwise `G` is edgeless and
   `χ ≤ 1`.
2. Let `H : G.Subgraph` be the subgraph carrying just that edge and its two ends.
   Then `χ(H.coe) = 2 = χ(G)`.
3. Criticality forbids `H < ⊤`, so `H = ⊤`: `G` is exactly one edge on two
   vertices, i.e. `G ≃g (⊤ : SimpleGraph (Fin 2))`.

*(←).*  `K₂` is 2-chromatic, and each proper subgraph is edgeless (drop the edge)
or a single vertex (drop a vertex), so `χ ≤ 1 < 2`.

**Reading.**  A 2-chromatic graph has at least one edge, and a single edge already
needs both colours; criticality leaves no room for anything else.

**Formalisation.**  `⊤ : SimpleGraph (Fin 2)` is `K₂`.  Step 3 is the shared
"a subgraph attaining `χ(G)` must be `⊤`" lemma noted under the 3-critical case. -/
theorem isKCritical_two_iff {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} :
    G.IsKCritical 2 ↔ Nonempty (G ≃g (⊤ : SimpleGraph (Fin 2))) := by
  sorry

-- Ex 8.1.8: no vertex cut of a k-critical graph induces a uniquely (k−1)-colourable subgraph
/-- **Exercise 8.1.8** (B&M §8.1, verbatim).  *A graph `G` is uniquely `k`-colourable
if any two `k`-colourings of `G` induce the same partition of `V`.  Show that no
vertex cut of a `k`-critical graph induces a uniquely `(k-1)`-colourable
subgraph.*

**Book proof.**  None — an exercise.

**Skeleton** (for `¬ (G.induce ↑S).UniquelyColorable (k-1)`).  This is theorem 8.2
with its step 4 replaced; steps 1, 2, 5, 6 below are *literally* theorem 8.2's, so
fill that first and share the work.
1. `intro huc`.  Get `G.Connected` from `IsCritical.connected hG.2`.
2. As in theorem 8.2: for each component `c` of `G - S`, the `S`-component `Gc` is
   a proper subgraph, so criticality gives `cc : Gc.coe.Coloring (Fin (k-1))`.
3. Each `cc` restricts to a `(k-1)`-colouring of `G.induce ↑S`.
4. **Where the hypotheses differ.**  `huc` says any two such restrictions induce
   the *same partition* of `S`.  Two colourings with equal `colorClasses` differ by
   a permutation of `Fin (k-1)`; compose each `cc` with the permutation carrying
   its restriction to a fixed reference one, so that all the `cc` now **agree on
   `S`**.
5. Glue: define `c* : G.Coloring (Fin (k-1))` by the common value on `S` and by
   `cc` off `S`; every edge lies inside some `Gc`, so `c*` is proper.
6. `χ(G) ≤ k - 1 < k`, contradicting `hG.1`.

**Reading.**  This generalises theorem 8.2 from clique cuts to uniquely colourable
ones, and isolates what theorem 8.2 was really using.  A clique cut forces the
vertices of `S` to take distinct colours; what the gluing actually needs is only
that the *partition* of `S` is forced, so that the pieces can be reconciled by
renaming colours.  Complete graphs are uniquely colourable, so theorem 8.2 is the
special case.

**Formalisation.**  The shared machinery worth extracting once: (i) an
`S`-component family indexed by `ConnectedComponent`, (ii) "every edge of `G` lies
in some `S`-component", and (iii) the gluing lemma turning agreement on `S` into a
colouring of `G`.  With those, theorem 8.2 and this exercise differ only in step 4.
`k - 1` is ℕ-subtraction; `hG.1` supplies `k ≥ 1`. -/
theorem IsKCritical.not_uniquelyColorable_of_isVertexCut {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] {G : SimpleGraph V} {k : ℕ} (hG : G.IsKCritical k)
    {S : Finset V} (hS : G.IsVertexCut S) :
    ¬ (G.induce (S : Set V)).UniquelyColorable (k - 1) := by
  sorry

-- Ex 8.1.9(a): in a critical graph, N(u) ⊄ N(v) for distinct u, v
/-- **Exercise 8.1.9(a)** (B&M §8.1, verbatim).  *Show that if `u` and `v` are two
vertices of a critical graph `G`, then `N(u) ⊄ N(v)`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `¬ (G.neighborSet u ⊆ G.neighborSet v)`).
1. `intro hsub`.  Set `k = χ(G)`; note `k ≥ 1`.
2. Let `H : G.Subgraph` be the induced subgraph on `({u}ᶜ : Set V)` — the book's
   `G - u`.  Then `H < ⊤`, so criticality gives `c : H.coe.Coloring (Fin (k-1))`.
3. `huv : u ≠ v` puts `v` in `H.verts`; let `j := c ⟨v, _⟩` be its colour.
4. **The key step.**  Extend `c` to `G` by `u ↦ j`.  Properness at `u`: let `w` be
   a neighbour of `u`.  Then `w ≠ u` (looplessness), so `w ∈ H.verts`, and
   `hsub` makes `w` a neighbour of `v`; since `c` is proper on `H`,
   `c w ≠ c v = j`.  Edges avoiding `u` are `c`'s own.
5. So `G.Colorable (k-1)`, giving `χ(G) ≤ k - 1 < k` — contradiction.

**Reading.**  In a critical graph no vertex is redundant, and a vertex whose
neighbourhood is contained in another's is exactly redundant: it can simply
inherit that vertex's colour.  Note the argument needs `u` and `v` *nonadjacent* to
work, and gets it for free — if `u ~ v` then `v ∈ N(u) ⊆ N(v)`, contradicting
looplessness.

**Formalisation.**  Stated with `¬ (… ⊆ …)`, matching the book's `⊄`.  `[Nonempty V]`
is needed to know `χ(G) ≥ 1` in step 1. -/
theorem IsCritical.neighborSet_not_subset {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} (h : G.IsCritical) {u v : V} (huv : u ≠ v) :
    ¬ (G.neighborSet u ⊆ G.neighborSet v) := by
  sorry

-- Ex 8.1.9(b): no k-critical graph has exactly k + 1 vertices
/-- **Exercise 8.1.9(b)** (B&M §8.1, verbatim).  *Deduce that no `k`-critical graph
has exactly `k + 1` vertices.*

**Book proof.**  None — an exercise; "deduce" points at part (a).

**Skeleton** (for `Fintype.card V ≠ k + 1`).
1. `intro hcard`.  Theorem 8.1 gives `k - 1 ≤ δ(G)`, so `k - 1 ≤ G.degree v` for
   every `v`.  Each vertex has at most `card V - 1 = k` neighbours, so every degree
   is `k - 1` or `k`.
2. Rephrase in the complement: `Gᶜ.degree v = k - G.degree v ≤ 1`, i.e. **`Gᶜ` has
   maximum degree at most `1`** — it is a matching.  (This is the book's "counting
   argument on the complement".)
3. **Case `Gᶜ` has no edge.**  Then `G = ⊤`, complete on `k + 1` vertices, so
   `χ(G) = k + 1 ≠ k`, contradicting `hG.1`.
4. **Case `Gᶜ` has an edge, `u ~ v` in `Gᶜ`.**  By step 2 neither `u` nor `v` has
   any other `Gᶜ`-neighbour, so in `G` both are adjacent to everything except each
   other and themselves:
   `G.neighborSet u = univ \ {u, v} = G.neighborSet v`.
5. In particular `G.neighborSet u ⊆ G.neighborSet v` with `u ≠ v`, contradicting
   part (a).

**Reading.**  So `k`-critical graphs come in sizes `k` (the complete graph `K_k`)
and `k + 2` or more, never `k + 1`.  The reason is that one vertex of slack forces
the complement to be a matching, and a matched pair has *identical*
neighbourhoods — the most extreme violation of part (a).  Exercise 8.1.12 asks for
4-critical graphs on `n` vertices for `n = 4` and all `n ≥ 6`; the gap at `n = 5`
is exactly this result.

**Formalisation.**  Step 2's degree identity `G.degree v + Gᶜ.degree v = card V - 1`
is the workhorse and is worth stating as its own `have`.  Take care that `k - 1` in
step 1 is ℕ-subtraction — the case `k = 0` should be dispatched separately (a
0-chromatic graph has an empty carrier, so `card V = 1` is impossible). -/
theorem no_isKCritical_card_eq_succ {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} {k : ℕ} (hG : G.IsKCritical k) : Fintype.card V ≠ k + 1 := by
  sorry

-- Ex 8.1.10(a): χ(G₁ ∨ G₂) = χ(G₁) + χ(G₂)
/-- **Exercise 8.1.10(a)** (B&M §8.1, verbatim).  *Show that
`χ(G₁ ∨ G₂) = χ(G₁) + χ(G₂)`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `(G.join H).chromaticNumber = G.chromaticNumber + H.chromaticNumber`).
Prove the two inequalities separately.
1. **`≤`.**  Take optimal colourings `cG : G.Coloring (Fin a)` and
   `cH : H.Coloring (Fin b)` with `a = χ(G)`, `b = χ(H)`.  Combine them into
   `G.join H → Fin a ⊕ Fin b` by `inl x ↦ inl (cG x)`, `inr y ↦ inr (cH y)`.
   Properness: within-side edges are handled by `cG`/`cH`; cross edges get colours
   in different summands, hence distinct.  So `χ(join) ≤ a + b`.
2. **`≥`.**  Let `c` be any colouring of `G.join H`.  The colour sets
   `A = c '' range inl` and `B = c '' range inr` are **disjoint**, since every
   `x : α` is adjacent to every `y : β` in the join.
3. `c ∘ inl` is a proper colouring of `G` using only `A`, so `χ(G) ≤ |A|`; likewise
   `χ(H) ≤ |B|`.  With disjointness, `χ(G) + χ(H) ≤ |A| + |B| = |A ∪ B| ≤` the
   number of colours `c` uses.  Taking `c` optimal gives `≥`.

**Reading.**  No colour can be used on both sides of a join, so the two palettes are
forced to be disjoint and the chromatic numbers simply add.  This makes joins a
convenient way to build graphs of prescribed chromatic number, and is why the wheel
`C_n ∨ K₁` needs `χ(C_n) + 1` colours.

**Formalisation.**  Addition is in `ℕ∞`; both summands are finite here (finite
carriers), so it is ordinary addition, but the casts still need care — extracting
`a`, `b` as naturals up front, as in step 1, keeps the arithmetic in `ℕ`.
`[Nonempty α]`, `[Nonempty β]` ensure both sides genuinely contribute. -/
theorem chromaticNumber_join {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    (G.join H).chromaticNumber = G.chromaticNumber + H.chromaticNumber := by
  sorry

-- Ex 8.1.10(b): G₁ ∨ G₂ is critical ⇔ both G₁ and G₂ are critical
/-- **Exercise 8.1.10(b)** (B&M §8.1, verbatim).  *Show that `G₁ ∨ G₂` is critical if
and only if both `G₁` and `G₂` are critical.*

**Book proof.**  None — an exercise.

**Skeleton** (for `(G.join H).IsCritical ↔ G.IsCritical ∧ H.IsCritical`).  Both
directions run on part (a), `χ(join) = χ(G) + χ(H)`.

*(→).*
1. Given `G' < ⊤` in `G.Subgraph`, build `K : (G.join H).Subgraph` as the join of
   `G'` with all of `H` (all cross edges between `G'.verts` and `β`).  Then
   `K < ⊤` because `G' < ⊤`.
2. Part (a) applied to `K.coe` gives `χ(K.coe) = χ(G'.coe) + χ(H)`; criticality of
   the join gives `χ(K.coe) < χ(G) + χ(H)`; cancel `χ(H)`.  Symmetrically for `H`.

*(←).*  Given `K < ⊤` in `(G.join H).Subgraph`, split on *how* `K` is proper.
3. **`K` omits a vertex or a within-side edge.**  Then its restriction to that side
   is `< ⊤` there; criticality of that side, plus monotonicity of `χ` under
   `K ≤ (restriction to α) ∨ (restriction to β)`, gives the strict drop.
4. **`K` has every vertex and every within-side edge, but omits a cross edge
   `x₀ y₀`.**  This is the case that needs an idea.  Criticality of `G` gives a
   `χ(G)`-colouring of `G` in which `x₀` is **alone in its class**: colour
   `G - x₀` with `χ(G) - 1` colours and give `x₀` a fresh one.  Do the same for
   `H` and `y₀`.  Now **merge** those two singleton classes into a single colour —
   legitimate precisely because `x₀ y₀` is the missing edge — producing a colouring
   of `K.coe` with `χ(G) + χ(H) - 1` colours.

**Reading.**  By part (a) the join's chromatic number is the sum, so a drop on one
side is a drop for the join.  This yields a construction for critical graphs of
large chromatic number: join known critical graphs.  For instance `K₁ ∨ C₅` is
4-critical, `C₅` being 3-critical (exercise 8.1.7) — this is exactly the family
exercise 8.1.12 asks for.

**Formalisation.**  Step 4 is the one that would be missed by reasoning only about
"remove a vertex or a within-side edge"; the subgraph lattice of a join contains
subgraphs that are not themselves joins, and they must be handled. -/
theorem join_isCritical_iff {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    (G.join H).IsCritical ↔ G.IsCritical ∧ H.IsCritical := by
  sorry

-- Ex 8.1.11 (Hajós): the Hajós construction preserves k-criticality (single-carrier encoding)
-- NOTE: outline's binder `{k v v₁ v₂ : _}` cannot elaborate (heterogeneous types under one hole);
-- restated with explicit `{k : ℕ} {v v₁ v₂ : V}`.
/-- **Exercise 8.1.11** (B&M §8.1, verbatim; G. Hajós).  *Let `G₁` and `G₂` be two
`k`-critical graphs with exactly one vertex `v` in common, and let `vv₁` and `vv₂`
be edges of `G₁` and `G₂`.  Show that the graph
`(G₁ - vv₁) ∪ (G₂ - vv₂) + v₁v₂` is `k`-critical.*

**Book proof.**  None — an exercise.

**Skeleton.**  Write `Ĝ` for the constructed graph.  Three obligations.
1. **`Ĝ` is not `(k-1)`-colourable.**  Suppose `c` were such a colouring.  The edge
   `v₁v₂` is present, so `c v₁ ≠ c v₂`; hence `c v` differs from at least one of
   them — say `c v ≠ c v₁`.  Restrict `c` to `G₁`'s support: the only edge of `G₁`
   absent from `Ĝ` is `vv₁`, and `c v ≠ c v₁` reinstates it, so the restriction is
   a `(k-1)`-colouring of `G₁`, contradicting `χ(G₁) = k`.  The case
   `c v ≠ c v₂` is symmetric with `G₂`.
2. **`Ĝ` is `k`-colourable.**  Take `k`-colourings `c₁` of `G₁` and `c₂` of `G₂`
   and permute `c₂`'s palette so that `c₁ v = c₂ v` *and* `c₁ v₁ ≠ c₂ v₂`.  Both
   are achievable: the first by any permutation matching the two colours at `v`,
   and the second — if it fails — by a further transposition moving `c₂ v₂` to a
   third colour, which exists once `k ≥ 3`.  Dispatch `k ≤ 2` separately (a
   2-critical graph is `K₂`, so `Ĝ` is a single edge plus an isolated vertex).
   Steps 1 and 2 together give `χ(Ĝ) = k`.
3. **`Ĝ` is critical.**  For `K < ⊤` in `Ĝ.Subgraph`, split on what is missing:
   * *the edge `v₁v₂`*: then `K ≤ (G₁ - vv₁) ∪ (G₂ - vv₂)`.  Criticality of `G₁`
     and `G₂` makes each side `(k-1)`-colourable; permute one palette to agree at
     the shared vertex `v` and glue.
   * *something inside `G₁`* (a vertex or edge other than `vv₁`): criticality of
     `G₁` gives a `(k-1)`-colouring of that part; extend across `v` to `G₂ - vv₂`,
     which is `(k-1)`-colourable by criticality of `G₂`, aligning at `v`.
   * *something inside `G₂`*: symmetric.

**Reading.**  Glue two `k`-critical graphs at a single vertex `v`, delete one edge
at `v` from each, and join the two orphaned endpoints `v₁`, `v₂` by a new edge; the
result is again `k`-critical.  Step 1 is the heart: the new edge forces `v₁` and
`v₂` apart, so `v` must agree with one of them, and that agreement is exactly what
repairs the deleted edge on that side.  The **Hajós construction** matters because,
iterated from `K_k`, it generates *every* graph with chromatic number at least `k`
— a complete but impractical characterisation.

**Formalisation.**  The outline's binder `{k v v₁ v₂ : _}` cannot elaborate
(heterogeneous types under one hole), so the statement uses explicit
`{k : ℕ} {v v₁ v₂ : V}`.  Both graphs live on **one** carrier `V`; "exactly one
vertex in common" is `hmeet : G₁.support ∩ G₂.support = {v}`, and each `Gᵢ`'s real
content is `Gᵢ.induce Gᵢ.support`, which is why the hypotheses are stated about the
induced graphs rather than about `G₁`, `G₂` directly.  Edge deletion is `\ edge`
and edge addition is `⊔ edge`. -/
theorem hajos_construction {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G₁ G₂ : SimpleGraph V} {k : ℕ} {v v₁ v₂ : V}
    (h₁ : (G₁.induce G₁.support).IsKCritical k) (h₂ : (G₂.induce G₂.support).IsKCritical k)
    (hmeet : G₁.support ∩ G₂.support = {v})
    (he₁ : G₁.Adj v v₁) (he₂ : G₂.Adj v v₂) :
    IsKCritical
      (((G₁ \ SimpleGraph.edge v v₁) ⊔ (G₂ \ SimpleGraph.edge v v₂)) ⊔ SimpleGraph.edge v₁ v₂)
      k := by
  sorry

-- Ex 8.1.12: a 4-critical graph on n vertices, for n = 4 and all n ≥ 6 (n = 5 impossible, 8.1.9b)
/-- **Exercise 8.1.12** (B&M §8.1, verbatim).  *For `n = 4` and all `n ≥ 6`,
construct a 4-critical graph on `n` vertices.*

**Book proof.**  None — an exercise, and a *construct* one: the content is
exhibiting a witness, not verifying an implication.

**Skeleton** (for `∃ G : SimpleGraph (Fin n), G.IsKCritical 4`).  Three cases,
covering `n = 4` and every `n ≥ 6`.
1. **`n = 4`.**  Take `G = ⊤`, i.e. `K₄`.  It is 4-chromatic, and every proper
   subgraph either drops a vertex (leaving `K₃`) or an edge, and is 3-colourable.
2. **`n` even, `n ≥ 6`.**  Take `K₁ ∨ C_{n-1}`, the wheel with an odd rim (`n - 1`
   is odd and `≥ 5`).  It is 4-critical by exercise 8.1.10(b): `K₁` is 1-critical
   (8.1.7) and `C_{n-1}` is 3-critical (8.1.7), so the join is critical, and
   8.1.10(a) gives `χ = 1 + 3 = 4`.
3. **`n` odd, `n ≥ 7`.**  Apply the Hajós construction (exercise 8.1.11) to `K₄`
   and the graph from case 1 or 2 on `n - 3` vertices — note `n - 3` is even and
   `≥ 4`, so it is covered, and Hajós on `a` and `b` vertices with one identified
   yields `a + b - 1 = 4 + (n-3) - 1 = n` vertices.  Exercise 8.1.11 gives that the
   result is again 4-critical.

**Reading.**  The excluded case `n = 5` is exactly exercise 8.1.9(b): no
`k`-critical graph has `k + 1` vertices, so no 4-critical graph has five.  The
book's figure 8.2 (the Grötzsch graph) is another witness, for `n = 11`.

**Formalisation.**  The carrier is pinned to `Fin n`, so each construction must be
transported along an explicit equivalence — `Fin 1 ⊕ Fin (n-1) ≃ Fin n` for case 2,
and the Hajós single-carrier encoding of exercise 8.1.11 for case 3.  That
transport, rather than the graph theory, is most of the Lean work here; a reusable
"`IsKCritical` transfers along `≃g`" lemma is worth having first. -/
theorem exists_isKCritical_four (n : ℕ) (hn : n = 4 ∨ 6 ≤ n) :
    ∃ G : SimpleGraph (Fin n), G.IsKCritical 4 := by
  sorry

-- Ex 8.1.13(a)* (Kainen): ≤ n − 1 cross edges ⇒ n-colourable  (hcut stated as #cross + 1 ≤ n)
open scoped Classical in
/-- **Exercise 8.1.13(a)*** (B&M §8.1, verbatim; P. C. Kainen).  *Let `(X, Y)` be a
partition of `V` such that `G[X]` and `G[Y]` are both `n`-colourable.  Show that,
if the edge cut `[X, Y]` has at most `n - 1` edges, then `G` is also
`n`-colourable.*

**Book proof.**  None — an exercise, and one the book **stars**.

**Skeleton** (for `G.Colorable n`).  A counting argument over the symmetric group.
1. From `hX`, `hY` obtain `cX : (G.induce X).Coloring (Fin n)` and
   `cY : (G.induce Xᶜ).Coloring (Fin n)`.
2. For each `σ : Equiv.Perm (Fin n)` define `c σ : V → Fin n` by `cX` on `X` and
   `σ ∘ cY` off `X`.  It is automatically proper on every edge with both ends on
   the same side — permuting a palette preserves properness.
3. Call a cross edge `s(x, y)` (with `x ∈ X`, `y ∉ X`) **bad for `σ`** when
   `σ (cY y) = cX x`.  For a *fixed* cross edge, the bad `σ` are those sending one
   specified point to one specified value: exactly `(n-1)!` of them.
4. **Count.**  Bad permutations number at most `#cross · (n-1)!`, and `hcut` gives
   `#cross ≤ n - 1`, so at most `(n-1) · (n-1)! < n! = |Equiv.Perm (Fin n)|`.
   Hence some `σ₀` is bad for no cross edge.
5. `c σ₀` is then proper on cross edges too, so it is an `n`-colouring of `G`.

**Reading.**  Colour each side separately; the two colourings may clash across the
cut, but there are at most `n - 1` cut edges and `n!` ways to relabel one side's
palette — far more freedom than there are constraints to violate.  A thin cut
therefore cannot force an extra colour.  Note how sharp the count is: `n` cut edges
would give `n · (n-1)! = n!`, exactly enough to rule out every permutation.

**Formalisation.**  `hcut` is stated as `#cross + 1 ≤ n` rather than
`#cross ≤ n - 1` to avoid ℕ-subtraction, and it carries `n ≥ 1` as a side benefit.
The partition `(X, Y)` is `X` and its complement, so `Y` never appears by name.
Step 4 needs `Fintype.card (Equiv.Perm (Fin n)) = n !` and the factorial identity
`n ! = n * (n-1)!`. -/
theorem kainen {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {X : Set V} {n : ℕ}
    (hX : (G.induce X).Colorable n) (hY : (G.induce (Xᶜ)).Colorable n)
    (hcut : (G.edgeFinset.filter fun e => ∃ x ∈ X, ∃ y ∉ X, e = s(x, y)).card + 1 ≤ n) :
    G.Colorable n := by
  sorry

-- Ex 8.1.13(b) (Dirac): every k-critical graph is (k−1)-edge-connected
/-- **Exercise 8.1.13(b)** (B&M §8.1, verbatim; G. A. Dirac).  *Deduce that every
`k`-critical graph is `(k-1)`-edge-connected.*

**Book proof.**  None — an exercise; "deduce" points at part (a).

**Skeleton** (for `k - 1 ≤ G.edgeConnectivity`).
1. `edgeConnectivity` is an `sInf` over sizes of edge cuts, so by
   `le_csInf`-style reasoning it suffices to show **every** edge cut `F` satisfies
   `k - 1 ≤ F.card`.
2. `by_contra`: take `F` with `F.card + 1 ≤ k - 1`.  By `IsEdgeCut`,
   `G.deleteEdges ↑F` is disconnected; let `X` be the vertex set of one of its
   components, so `X` and `Xᶜ` are both nonempty.
3. **Every `G`-edge across `(X, Xᶜ)` lies in `F`** — otherwise it would survive the
   deletion and join the two sides.  Hence `#[X, Xᶜ] ≤ F.card`.
4. `G.induce X` and `G.induce Xᶜ` are *proper* subgraphs of `G` (each misses the
   other side, which is nonempty), so criticality makes both `(k-1)`-colourable.
5. Apply part (a) with `n = k - 1`: its hypothesis `#cross + 1 ≤ n` is steps 3 and
   2 chained.  Conclusion: `G.Colorable (k-1)`.
6. So `χ(G) ≤ k - 1 < k`, contradicting `hG.1`.

**Reading.**  Criticality forces robust connectivity: a graph that *minimally* needs
`k` colours cannot be pulled apart by fewer than `k - 1` edge deletions.  This sits
alongside theorem 8.1, which gives the corresponding degree bound `δ ≥ k - 1`, and
corollary 8.2, which rules out cut vertices — three different senses in which a
critical graph is tightly held together.

**Formalisation.**  The conclusion `k - 1 ≤ edgeConnectivity` *is* the definition of
`(k-1)`-edge-connected (B&M §3.1: `G` is `k`-edge-connected if `κ' ≥ k`), so no
separate predicate is needed.  Step 1 relies on `sInf ∅ = 0` being harmless: if `G`
has no edge cut at all the bound must still be proved, and there step 2 has nothing
to work with — dispatch that case by noting a graph with no edge cut is complete or
trivial. -/
theorem IsKCritical.edgeConnectivity_ge {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} {k : ℕ} (hG : G.IsKCritical k) :
    k - 1 ≤ G.edgeConnectivity := by
  sorry

/-! ## §8.1 — Brooks and its equivalents (2 items route to the orchestrator) -/

-- Thm 8.4 (BROOKS): connected, not an odd cycle, not complete ⇒ χ ≤ Δ  (0 hits in Mathlib)
/-- **Theorem 8.4** (Brooks, 1941; proof by Lovász, 1973).  *If `G` is a connected
simple graph and is neither an odd cycle nor a complete graph, then `χ ≤ Δ`.*

**Book proof** (B&M §8.2, verbatim).  *Let `G` be a `k`-chromatic graph which
satisfies the hypothesis of the theorem.  Without loss of generality, we may assume
that `G` is `k`-critical.  By corollary 8.2, `G` is a block.  Also, since
1-critical and 2-critical graphs are complete and 3-critical graphs are odd cycles
(exercise 8.1.7), we have `k ≥ 4`.*

*If `G` has a 2-vertex cut `{u, v}`, corollary 8.3 gives*

    2Δ ≥ d(u) + d(v) ≥ 3k - 5 ≥ 2k - 1

*This implies that `χ = k ≤ Δ`, since `2Δ` is even.*

*Assume, then, that `G` is 3-connected.  Since `G` is not complete, there are
three vertices `u`, `v` and `w` in `G` such that `uv, vw ∈ E` and `uw ∉ E`
(exercise 1.6.14).  Set `u = v₁` and `w = v₂` and let `v₃, v₄, …, v_ν = v` be any
ordering of the vertices of `G - {u, w}` such that each `vᵢ` is adjacent to some
`vⱼ` with `j > i`.  (This can be achieved by arranging the vertices of `G - {u, w}`
in nonincreasing order of their distance from `v`.)  We can now describe a
`Δ`-colouring of `G`: assign colour 1 to `v₁ = u` and `v₂ = w`; then successively
colour `v₃, v₄, …, v_ν`, each with the first available colour in the list
`1, 2, …, Δ`.  By the construction of the sequence `v₁, v₂, …, v_ν`, each vertex
`vᵢ`, `1 ≤ i ≤ ν - 1`, is adjacent to some vertex `vⱼ` with `j > i`, and therefore
to at most `Δ - 1` vertices `vⱼ` with `j < i`.  It follows that, when its turn
comes to be coloured, `vᵢ` is adjacent to at most `Δ - 1` colours, and thus that
one of the colours `1, 2, …, Δ` will be available.  Finally, since `v_ν` is
adjacent to two vertices of colour 1 (namely `v₁` and `v₂`), it is adjacent to at
most `Δ - 2` other colours and can be assigned one of the colours `2, 3, …, Δ`.*

**Skeleton** (for `χ(G) ≤ G.maxDegree`).  The hardest item in the file; expect to
build it as several standalone lemmas rather than one ladder.
1. **Reduce to the critical case.**  Set `k = χ(G)`.  By `exists_isKCritical_subgraph`
   take `H ≤ G` with `H.coe` `k`-critical.  Since `χ(H.coe) = χ(G)` and
   `H.coe.maxDegree ≤ G.maxDegree`, it suffices to bound `k` by `H.coe.maxDegree`.
   *Care:* `H.coe` must still satisfy the hypotheses — it is connected (corollary
   8.2) but "not an odd cycle / not complete" must be re-established, and this is
   the one place the book's "without loss of generality" hides work.
2. **`k ≥ 4`.**  Exercise 8.1.7 in all three cases: `k = 1, 2` make `H.coe`
   complete and `k = 3` makes it an odd cycle, each contradicting `hnotcomplete` /
   `hnotcycle` after step 1.
3. **Case A: `H.coe` has a 2-vertex cut `{u, v}`.**  Corollary 8.3 gives
   `3k ≤ d(u) + d(v) + 5 ≤ 2Δ + 5`.  With `k ≥ 4` this yields `2k ≤ 2Δ + 1`, and
   since the left side is even, `2k ≤ 2Δ`, i.e. `k ≤ Δ`.  (The parity step is the
   book's "since `2Δ` is even"; in ℕ it is `Nat.lt_of_succ_le` plus evenness.)
4. **Case B: `H.coe` is 3-connected.**  Three sub-steps.
   * **The triple.**  Not complete plus connected gives `u, v, w` with `uv, vw ∈ E`
     and `uw ∉ E` (exercise 1.6.14).  Prove this separately: take nonadjacent `u`,
     `w` at distance 2 and let `v` be a common neighbour.
   * **The ordering.**  Enumerate `V` as `v₁ = u`, `v₂ = w`, then the rest in
     *nonincreasing distance from `v`*, ending at `v_ν = v`.  The property to
     extract is: every `vᵢ` with `i < ν` has a neighbour `vⱼ` with `j > i`.  For
     `i ≥ 3` this is because a vertex at distance `d > 0` from `v` has a neighbour
     at distance `d - 1`, which comes later; for `i = 1, 2` it is 3-connectedness
     of `H.coe` that keeps `u` and `w` attached to the rest.
   * **The greedy colouring.**  Colour `v₁` and `v₂` both `1` (legitimate: `uw ∉ E`),
     then greedily.  Each `vᵢ` (`i < ν`) has a *later* neighbour, hence at most
     `Δ - 1` earlier ones, so a colour is free.  At `v_ν = v`, both `v₁` and `v₂`
     are neighbours and share colour `1`, so at most `Δ - 1` distinct colours are
     blocked and one of `1, …, Δ` is free.

**Reading.**  Corollary 8.1.2 gives `χ ≤ Δ + 1` for every graph; Brooks says only
*two families* attain it — odd cycles (`χ = 3 = Δ + 1`) and complete graphs
(`χ = n = Δ + 1`).  Everything else needs only `Δ` colours.  The book contrasts
this with Vizing's theorem 6.2, where *many* graphs satisfy `χ' = Δ + 1`.  The
trick of the proof is the ordering: by ending at a vertex two of whose neighbours
were forced to share a colour, the greedy algorithm is given one unit of slack
exactly where it would otherwise run out.

**Formalisation.**  0 hits in Mathlib — this is a genuine build.  `hnotcycle` is
stated as `∀ n, Odd n → IsEmpty (G ≃g cycleGraph n)`, i.e. `G` is isomorphic to no
odd cycle; `hnotcomplete` as `G ≠ ⊤`.  Both are consumed only in step 2.  Step 1's
caveat is worth taking seriously before starting: the reduction to the critical
subgraph is stated casually by the book but is not free in Lean. -/
theorem brooks_chromaticNumber_le_maxDegree
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hnotcycle : ∀ (n : ℕ), Odd n → IsEmpty (G ≃g cycleGraph n))
    (hnotcomplete : G ≠ ⊤) :
    G.chromaticNumber ≤ G.maxDegree := by
  sorry

-- Ex 8.2.1: Brooks ⇔ (k-critical, k ≥ 4, not complete ⇒ 2ε ≥ ν(k−1) + 1).  (Type-pinned.)
/-- **Exercise 8.2.1** (B&M §8.2, verbatim).  *Show that Brooks' theorem is equivalent
to the following statement: if `G` is `k`-critical (`k ≥ 4`) and not complete, then
`2ε ≥ ν(k-1) + 1`.*

**Book proof.**  None — an exercise.

**Skeleton** (an `↔` between two universally quantified statements; prove each
direction by instantiating the other at the right graph).

*(→) Brooks implies the edge bound.*
1. Assume Brooks and let `G` be `k`-critical, `k ≥ 4`, not complete.
2. `G` is connected (`IsCritical.connected`) and is not an odd cycle — an odd cycle
   is 3-critical (exercise 8.1.7), while `k ≥ 4`.  So Brooks applies: `k ≤ Δ`.
3. Theorem 8.1 gives `k - 1 ≤ δ`, hence `ν(k-1) ≤ ∑ v, d(v) = 2ε` (handshake).
4. For the extra `+1`: step 2 supplies a vertex of degree `Δ ≥ k > k - 1`, so the
   sum in step 3 is *strictly* larger than `ν(k-1)`, giving `ν(k-1) + 1 ≤ 2ε`.

*(←) The edge bound implies Brooks.*
5. Assume the bound; let `G` be connected, not an odd cycle, not complete, and set
   `k = χ(G)`.  Reduce to `G` `k`-critical as in Brooks step 1.
6. `k ≥ 4` by exercise 8.1.7 (as in Brooks step 2); `G` not complete by hypothesis.
   So the bound gives `ν(k-1) + 1 ≤ 2ε`.
7. If every vertex had degree `≤ k - 1`, handshaking would give `2ε ≤ ν(k-1)`,
   contradicting step 6.  So some vertex has degree `≥ k`, i.e. `Δ ≥ k = χ`.

**Reading.**  Theorem 8.1 already gives `2ε ≥ ν(k-1)` for a `k`-critical graph; the
exercise's content is the extra `+1`, which says the bound is never *exactly*
attained — not every vertex can have degree exactly `k - 1`.  That is precisely
Brooks in disguise: a `(k-1)`-regular critical graph would have `χ = k = Δ + 1`,
which Brooks forbids outside the two exceptional families.

**Formalisation.**  Both sides are pinned to `Type` (not `Type*`) so that the two
quantifications range over the same universe and the `↔` is well-formed.  Note the
statement quantifies over graphs, so each direction *instantiates* the assumed side
at a graph it constructs — this is an equivalence of schemas, not of propositions
about one fixed `G`. -/
theorem brooks_iff_edge_bound :
    (∀ {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.Connected → (∀ n, Odd n → IsEmpty (G ≃g cycleGraph n)) → G ≠ ⊤ →
        G.chromaticNumber ≤ G.maxDegree)
    ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
        {k : ℕ}, G.IsKCritical k → 4 ≤ k → G ≠ ⊤ →
        Fintype.card V * (k - 1) + 1 ≤ 2 * G.edgeFinset.card) := by
  sorry

-- Ex 8.2.2 (RESTATED): Δ = 3 ⇒ χ′ ≤ 4, with χ′ spelled as χ(lineGraph).  (Simple-graph weakening.)
/-- **Exercise 8.2.2** (B&M §8.2, verbatim).  *Use Brooks' theorem to show that if `G`
is loopless with `Δ = 3`, then `χ' ≤ 4`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `(G.lineGraph).chromaticNumber ≤ 4`).
1. **Bound the line graph's maximum degree.**  An edge `s(x,y)` of `G` is adjacent
   in `L(G)` exactly to the other edges at `x` and at `y`, so
   `L(G).degree s(x,y) = (d(x) - 1) + (d(y) - 1) ≤ (3-1) + (3-1) = 4`.  Hence
   `L(G).maxDegree ≤ 4`.  This is the only place `h : G.maxDegree = 3` is used.
2. **Apply Brooks to `L(G)`**, which needs its three hypotheses:
   * *connected* — `L(G)` need **not** be connected, so first reduce to components:
     `χ` of a graph is the sup of `χ` over its components (the same lemma as
     `IsCritical.connected` step 3), and it is enough to bound each.
   * *not complete* — if a component of `L(G)` is complete, bound `χ` directly by
     its vertex count; with `Δ(L(G)) ≤ 4` a complete component has at most `5`
     vertices, and the case `K₅` is excluded because `K₅` is not a line graph of a
     `Δ = 3` graph (its vertices would need degree `4`, forcing a vertex of degree
     `3` on both ends).
   * *not an odd cycle* — an odd cycle has `χ = 3 ≤ 4` directly.
3. In the remaining case Brooks gives `χ(component) ≤ Δ(component) ≤ 4`.
4. Recombine over components for `χ(L(G)) ≤ 4`.

**Reading.**  The edge chromatic number `χ'(G)` is the chromatic number of the line
graph `L(G)`, whose vertices are the edges of `G` with adjacency "shares an end".
So Brooks' *vertex*-colouring theorem yields an *edge*-colouring bound, recovering
for cubic graphs what Vizing's theorem 6.2 gives in general.

**Formalisation.**  Two departures from the book, both weakenings.  (i) `χ'` is
spelled as `χ(lineGraph)`; there is no separate `chromaticIndex` here.  (ii) The
book says *loopless*, which in B&M permits parallel edges; `SimpleGraph` has none,
so this is the simple-graph case only.  With multiplicities the degree count in
step 1 is unchanged, but `lineGraph` would have to be redefined, so the weakening
is deliberate.  Note also that the exercise is stated with `Δ = 3` exactly, not
`Δ ≤ 3`; only `≤` is used. -/
theorem chromaticIndex_le_four_of_maxDegree_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.maxDegree = 3) :
    (G.lineGraph).chromaticNumber ≤ 4 := by
  sorry

/-! ## §8.3 — 2-vertex cut structure and K₄-subdivisions (Thm 8.3, Thm 8.5 route to orchestrator) -/

-- Thm 8.3 (Dirac 1953): structure of a k-critical graph at a 2-vertex cut.  Needs `contractEdge`.
/-- **Theorem 8.3** (Dirac, 1953).  *Let `G` be a `k`-critical graph with a 2-vertex
cut `{u, v}`.  Then (i) `G = G₁ ∪ G₂`, where `Gᵢ` is a `{u,v}`-component of type
`i` (`i = 1, 2`), and (ii) both `G₁ + uv` and `G₂ · uv` are `k`-critical* (where
`G₂ · uv` identifies `u` and `v`).

**Book proof** (B&M §8.1, verbatim).  *(i) Since `G` is critical, each
`{u, v}`-component of `G` is `(k-1)`-colourable.  Now there cannot exist
`(k-1)`-colourings of these `{u, v}`-components all of which agree on `{u, v}`,
since such colourings would together yield a `(k-1)`-colouring of `G`.  Therefore
there are two `{u, v}`-components `G₁` and `G₂` such that no `(k-1)`-colouring of
`G₁` agrees with any `(k-1)`-colouring of `G₂`.  Clearly one, say `G₁`, must be of
type 1 and the other, `G₂`, of type 2.  Since `G₁` and `G₂` are of different types,
the subgraph `G₁ ∪ G₂` of `G` is not `(k-1)`-colourable.  Therefore, because `G` is
critical, we must have `G = G₁ ∪ G₂`.*

*(ii) Set `H₁ = G₁ + uv`.  Since `G₁` is of type 1, `H₁` is `k`-chromatic.  We
shall prove that `H₁` is critical by showing that, for every edge `e` of `H₁`,
`H₁ - e` is `(k-1)`-colourable.  This is clearly so if `e = uv`, since then
`H₁ - e = G₁`.  Let `e` be some other edge of `H₁`.  In any `(k-1)`-colouring of
`G - e`, the vertices `u` and `v` must receive different colours, since `G₂` is a
subgraph of `G - e`.  The restriction of such a colouring to the vertices of `G₁`
is a `(k-1)`-colouring of `H₁ - e`.  Thus `G₁ + uv` is `k`-critical.  An analogous
argument shows that `G₂ · uv` is `k`-critical.*

**Skeleton.**  Follows the book part for part.

*(i) — the splitting.*
1. Criticality makes every `{u,v}`-component `(k-1)`-colourable (each is a proper
   subgraph, since a 2-vertex cut leaves at least two components).
2. If *all* components admitted colourings agreeing on `{u, v}`, the gluing lemma
   of theorem 8.2 would produce a `(k-1)`-colouring of `G`, contradicting `hG.1`.
   So two components `c₁`, `c₂` admit no agreeing pair.
3. `u` and `v` are nonadjacent (`IsCritical.not_adj_of_isVertexCut_pair`), so a
   colouring of a component may in principle give them equal or different colours.
   Failure to agree in *any* combination forces one component to be type 1 and the
   other type 2 — this is the book's "clearly", and is a small case analysis on the
   four possible combinations.
4. `uvComponent c₁ ⊔ uvComponent c₂` is not `(k-1)`-colourable (type 1 and type 2
   conflict on `{u, v}`), so criticality forbids it from being `< ⊤`; hence it is
   `⊤`, which is conjunct (i) of the goal.

*(ii) — the two `k`-critical graphs.*
5. `H₁ := G₁.coe ⊔ edge u v` is `k`-chromatic: `≤ k` since `H₁ ≤ G` up to the added
   edge, and `≥ k` because type 1 means every `(k-1)`-colouring of `G₁` equates `u`
   and `v`, which the new edge forbids.
6. `H₁` is critical.  By the reduction in the note below it suffices to check
   single-edge deletions.  For `e = uv`, `H₁ - e = G₁.coe`, `(k-1)`-colourable by
   step 1.  For any other `e`, take a `(k-1)`-colouring of `G - e` (criticality of
   `G`); `G₂ ⊆ G - e` is type 2, so it separates `u` and `v`; restricting to `G₁`
   colours `H₁ - e`.
7. Repeat for `H₂ := (G₂.coe).contractEdge u v`, with the roles of "same colour"
   and "different colour" exchanged: type 2 means every `(k-1)`-colouring separates
   `u` and `v`, which contraction forbids.

**Reading.**  At a 2-vertex cut a critical graph splits into exactly two pieces with
*opposite* demands on `u` and `v` — one insisting they agree, the other that they
differ.  That is why the cut cannot be repaired, and it is the structural fact that
both Brooks' theorem (via corollary 8.3) and theorem 8.5 exploit.

**Formalisation.**  Worth proving first, and reused in step 6: **for `k ≥ 2`,
criticality can be checked on single-edge deletions alone.**  Any `H < ⊤` is
contained in some `⊤ \ edge e`, and `χ` is monotone, so `χ(H.coe) ≤ χ(⊤ \ edge e)`;
vertex deletions are subsumed because a critical graph has `δ ≥ k - 1 ≥ 1`
(theorem 8.1), so every vertex carries an edge.  This closes the gap between the
book's edge-only check and the `Subgraph`-lattice definition of `IsCritical`.

The `(by simp [uvComponent])` arguments in the statement are the membership proofs
`u, v ∈ (uvComponent …).verts`, discharged by unfolding — the `{u, v}` is glued
onto every component by construction. -/
theorem kCritical_two_vertex_cut_structure
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {G : SimpleGraph V}
    {k : ℕ} (hG : G.IsKCritical k) {u v : V} (huv : u ≠ v)
    (hcut : G.IsVertexCut ({u, v} : Finset V)) :
    ∃ (c₁ c₂ : (G.induce ({u, v}ᶜ : Set V)).ConnectedComponent) (_ : c₁ ≠ c₂),
      -- (i)
      G.uvComponent u v c₁ ⊔ G.uvComponent u v c₂ = ⊤ ∧
      (G.uvComponent u v c₁).IsType1 u v (by simp [uvComponent]) (by simp [uvComponent]) k ∧
      (G.uvComponent u v c₂).IsType2 u v (by simp [uvComponent]) (by simp [uvComponent]) k ∧
      -- (ii)
      ((G.uvComponent u v c₁).coe ⊔ SimpleGraph.edge
          ⟨u, by simp [uvComponent]⟩ ⟨v, by simp [uvComponent]⟩).IsKCritical k ∧
      ((G.uvComponent u v c₂).coe.contractEdge
          ⟨u, by simp [uvComponent]⟩ ⟨v, by simp [uvComponent]⟩).IsKCritical k := by
  sorry

-- Cor 8.3: d(u) + d(v) ≥ 3k − 5, stated additively to dodge ℕ truncation
/-- **Corollary 8.3.**  *Let `G` be a `k`-critical graph with a 2-vertex cut
`{u, v}`.  Then `d(u) + d(v) ≥ 3k - 5`.*

**Book proof** (B&M §8.1, verbatim).  *Let `G₁` be the `{u, v}`-component of type 1
and `G₂` the `{u, v}`-component of type 2.  Set `H₁ = G₁ + uv` and `H₂ = G₂ · uv`.
By theorems 8.3 and 8.1*

    d_{H₁}(u) + d_{H₁}(v) ≥ 2k - 2   and   d_{H₂}(w) ≥ k - 1

*where `w` is the new vertex obtained by identifying `u` and `v`.  It follows that*

    d_{G₁}(u) + d_{G₁}(v) ≥ 2k - 4   and   d_{G₂}(u) + d_{G₂}(v) ≥ k - 1

*These two inequalities yield (8.1).*

**Skeleton** (for `3 * k ≤ G.degree u + G.degree v + 5`).
1. Theorem 8.3 supplies the type-1 component `G₁` and type-2 component `G₂`, with
   `H₁ = G₁ + uv` and `H₂ = G₂ · uv` both `k`-critical, and `G = G₁ ∪ G₂`.
2. Theorem 8.1 on `H₁`: every degree is `≥ k - 1`, so in particular
   `d_{H₁}(u) + d_{H₁}(v) ≥ 2k - 2`.
3. **Translate off the added edge.**  `d_{H₁}(u) = d_{G₁}(u) + 1` and likewise at
   `v`, since `uv ∉ G₁` (the two are nonadjacent in `G`).  Hence
   `d_{G₁}(u) + d_{G₁}(v) ≥ 2k - 4`.
4. Theorem 8.1 on `H₂`: the merged vertex `w` has `d_{H₂}(w) ≥ k - 1`.
5. **Translate off the contraction.**  `d_{H₂}(w) = d_{G₂}(u) + d_{G₂}(v)`: the
   neighbours of `w` are those of `u` together with those of `v`, with no double
   count (`u`, `v` share no neighbour inside `G₂`… *check this*) and no loop
   (`u ≁ v`).  Hence `d_{G₂}(u) + d_{G₂}(v) ≥ k - 1`.
6. **Recombine.**  `G = G₁ ∪ G₂` with `G₁ ∩ G₂ = {u, v}` and no edges between the
   two sides, so `d_G(u) = d_{G₁}(u) + d_{G₂}(u)` and likewise at `v`.  Adding
   steps 3 and 5 gives `d(u) + d(v) ≥ (2k - 4) + (k - 1) = 3k - 5`.

**Reading.**  This inequality is precisely what Brooks' theorem uses to dispose of
the 2-vertex-cut case: combined with `d(u), d(v) ≤ Δ` it forces `2Δ ≥ 3k - 5`,
which for `k ≥ 4` already gives `k ≤ Δ`.

**Formalisation.**  Stated additively as `3k ≤ d(u) + d(v) + 5` rather than
`d(u) + d(v) ≥ 3k - 5`, because ℕ-subtraction would truncate `3k - 5` to `0` for
`k ≤ 1` and make the statement vacuous exactly where it should be informative.
Step 5 deserves care: if `u` and `v` had a common neighbour in `G₂`, contracting
would merge two edges into one and the degree identity would fail — establish that
they do not, or weaken the identity to the inequality actually needed. -/
theorem kCritical_two_vertex_cut_degree_sum
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (hG : G.IsKCritical k) {u v : V} (huv : u ≠ v)
    (hcut : G.IsVertexCut ({u, v} : Finset V)) :
    3 * k ≤ G.degree u + G.degree v + 5 := by
  sorry

-- Thm 8.5 (Dirac 1952): 4-chromatic ⇒ contains a subdivision of K₄
/-- **Theorem 8.5** (Dirac, 1952).  *If `G` is 4-chromatic, then `G` contains a
subdivision of `K₄`* — the case `k = 4` of Hajós' conjecture.

**Book proof** (B&M §8.3, verbatim).  *Let `G` be a 4-chromatic graph.  Note that if
some subgraph of `G` contains a subdivision of `K₄`, then so, too, does `G`.
Without loss of generality, therefore, we may assume that `G` is critical, and
hence that `G` is a block with `δ ≥ 3`.  If `ν = 4`, then `G` is `K₄` and the
theorem holds trivially.  We proceed by induction on `ν`.  Assume the theorem true
for all 4-chromatic graphs with fewer than `n` vertices, and let `ν(G) = n > 4`.*

*Suppose, first, that `G` has a 2-vertex cut `{u, v}`.  By theorem 8.3, `G` has two
`{u, v}`-components `G₁` and `G₂`, where `G₁ + uv` is 4-critical.  Since
`ν(G₁ + uv) < ν(G)`, we can apply the induction hypothesis and deduce that
`G₁ + uv` contains a subdivision of `K₄`.  It follows that, if `P` is a
`(u, v)`-path in `G₂`, then `G₁ ∪ P` contains a subdivision of `K₄`.  Hence so,
too, does `G`, since `G₁ ∪ P ⊆ G`.*

*Now suppose that `G` is 3-connected.  Since `δ ≥ 3`, `G` has a cycle `C` of length
at least four.  Let `u` and `v` be nonconsecutive vertices on `C`.  Since
`G - {u, v}` is connected, there is a path `P` in `G - {u, v}` connecting the two
components of `C - {u, v}`; we may assume that the origin `x` and the terminus `y`
are the only vertices of `P` on `C`.  Similarly, there is a path `Q` in
`G - {x, y}` (see figure 8.6).*

*If `P` and `Q` have no vertex in common, then `C ∪ P ∪ Q` is a subdivision of `K₄`
(figure 8.6a).  Otherwise, let `w` be the first vertex of `P` on `Q`, and let `P'`
denote the `(x, w)`-section of `P`.  Then `C ∪ P' ∪ Q` is a subdivision of `K₄`
(figure 8.6b).  Hence, in both cases, `G` contains a subdivision of `K₄`.*

**Skeleton** (for `G.HasK4Subdivision`).
1. **Reduce to the critical case.**  Prove first, as a standalone lemma, that
   `HasK4Subdivision` is monotone: if `H ≤ G` and `H.coe` has one, so does `G`
   (map the six walks along the inclusion hom).  Then replace `G` by a 4-critical
   subgraph (`exists_isKCritical_subgraph`), which is a block (corollary 8.2) with
   `δ ≥ 3` (theorem 8.1 with `k = 4`).
2. **Strong induction on `Fintype.card V`.**  Base `ν = 4`: `δ ≥ 3` on four vertices
   forces `G = K₄`; take the six edges themselves as the six paths, all interiors
   empty, so the disjointness conditions hold trivially.
3. **Case A: `G` has a 2-vertex cut `{u, v}`.**  Theorem 8.3 gives `G₁ + uv`
   4-critical on fewer vertices; the induction hypothesis puts a `K₄`-subdivision
   in it.  If that subdivision uses the edge `uv`, replace it by a `(u,v)`-path `P`
   inside `G₂` (which exists: `G₂` is connected and contains both `u` and `v`).
   The result lives in `G₁ ∪ P ⊆ G`.  *The fiddly part is re-establishing internal
   disjointness after the substitution* — `P`'s interior lies in `G₂` and so misses
   `G₁` entirely, which is exactly what makes it work.
4. **Case B: `G` is 3-connected.**  Four sub-steps.
   * `δ ≥ 3` yields a cycle `C` of length `≥ 4`.
   * Pick nonconsecutive `u, v` on `C`.  `G - {u, v}` is connected (3-connectedness),
     so there is a path `P` between the two arcs of `C - {u, v}`; trim it so its
     ends `x`, `y` are its only vertices on `C`.
   * Likewise a path `Q` between the two arcs of `C - {x, y}`, in `G - {x, y}`.
   * If `P ∩ Q = ∅`, the branch vertices are `x, y, u, v` and the six paths are the
     four arcs of `C` together with `P` and `Q`.  Otherwise let `w` be the first
     vertex of `P` on `Q` and `P'` the `(x, w)`-section; the branch vertices become
     `x, w, u, v`.

**Reading.**  This is the case `k = 4` of Hajós' conjecture, settled by Dirac
(1952).  The book notes the conjecture in general is *known to be a very difficult
problem*, and mentions Hadwiger's related conjecture, whose case `k = 5` Wagner
showed equivalent to the four-colour conjecture of chapter 9.

**Formalisation.**  Step 1's monotonicity lemma is what licenses the book's
"without loss of generality" and should be built first — without it the reduction
to the critical subgraph is not available.  The induction in step 2 is on the
carrier's cardinality, but cases A and B produce graphs on *different carriers*
(subgraph coercions), so the induction is cleanest stated over all graphs on all
carriers of bounded size rather than over subgraphs of a fixed `G`. -/
theorem fourChromatic_hasK4Subdivision
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {G : SimpleGraph V}
    (h : G.chromaticNumber = 4) :
    G.HasK4Subdivision := by
  sorry

-- Ex 8.3.1*: ≤ 1 vertex of degree < 3 ⇒ K₄-subdivision
/-- **Exercise 8.3.1*** (B&M §8.3, verbatim).  *Show that if `G` is simple and has at
most one vertex of degree less than three, then `G` contains a subdivision of
`K₄`.*

**Book proof.**  None — an exercise, and one the book **stars**.

**⚠ Statement repaired — deviates from the book.**  The book's statement is **false**
on tiny carriers.  For `card V ≤ 1` the filtered set has at most one element, so
`h` holds, but `HasK4Subdivision` needs four distinct vertices and fails.
(`card V ∈ {2, 3}` is fine: there `h` itself is unsatisfiable, since every degree
is then `< 3`.)  The hypothesis `hv : 4 ≤ Fintype.card V` has therefore been
**added** to the signature, matching exercise 8.3.2(a) next door.  This is a
deliberate divergence from B&M, recorded here so it is not mistaken for a
transcription slip.

**Skeleton** (for `G.HasK4Subdivision`, given `hv`).
1. **Reduce to minimum degree `≥ 3`.**  If some vertex `v` has degree `< 3`, delete
   it: by `h` every *other* vertex has degree `≥ 3`, so `G - v` has minimum degree
   `≥ 3 - 1 = 2` — not yet enough.  Better: apply `h` directly, noting that at most
   one vertex is deficient, and handle that vertex by the monotonicity lemma of
   theorem 8.5 step 1 once a subdivision is found in `G - v`.
2. **The core (`δ ≥ 3` ⟹ `K₄`-subdivision).**  This is exactly case B of theorem
   8.5, and should be extracted from that proof as a standalone lemma rather than
   redone: `δ ≥ 3` gives a cycle `C` of length `≥ 4`; two internally disjoint paths
   across `C` complete the subdivision, with the "first crossing vertex" fallback
   when they meet.
3. Note that case B of theorem 8.5 also used 3-connectedness, to know `G - {u, v}`
   is connected.  Here only `δ ≥ 3` is available, so the extraction in step 2 must
   first be strengthened to work from minimum degree alone — this is where the
   star sits.

**Reading.**  Essentially-all vertices having degree at least three is enough to
force a topological `K₄`, with no colouring hypothesis at all.  So this is a purely
degree-theoretic sufficient condition where theorem 8.5 gives a chromatic one.
Neither is necessary: a subdivision of `K₄` can occur in graphs that are only
3-chromatic — the book's own example, a 4-cycle being a subdivision of `K₃`, makes
the analogous point one dimension down.

**Formalisation.**  "At most one vertex of degree less than three" is a `Finset`
cardinality bound on `univ.filter (fun v => G.degree v < 3)`.  This is the
statement exercise 8.3.2(a) reduces to, so filling that one first is not an
option — the dependency runs this way. -/
theorem hasK4Subdivision_of_few_low_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hv : 4 ≤ Fintype.card V)
    (h : (Finset.univ.filter fun v => G.degree v < 3).card ≤ 1) :
    G.HasK4Subdivision := by
  sorry

-- Ex 8.3.2(a)*: ν ≥ 4, ε ≥ 2ν − 2 ⇒ K₄-subdivision  (restated additively: 2ν ≤ ε + 2)
/-- **Exercise 8.3.2(a)*** (B&M §8.3, verbatim).  *Show that if `G` is simple with
`ν ≥ 4` and `ε ≥ 2ν - 2`, then `G` contains a subdivision of `K₄`.*

**Book proof.**  None — an exercise, and one the book **stars**.

**Skeleton** (for `G.HasK4Subdivision`, given `4 ≤ ν` and `2ν ≤ ε + 2`).
1. **Strong induction on `ν`**, with the hypothesis `2ν ≤ ε + 2` carried along.
2. **If some vertex `v` has degree `≤ 2`, delete it.**  Then `ν` drops by `1` and
   `ε` drops by at most `2`, so `2(ν - 1) ≤ (ε - 2) + 2` still holds: the invariant
   `2ν - ε ≤ 2` is preserved.  Apply the induction hypothesis to `G - v` and lift
   the subdivision back with the monotonicity lemma (theorem 8.5 step 1).
   * The induction must not fall below `ν = 4`.  Check: at `ν = 4` the hypothesis
     gives `ε ≥ 6`, so `G = K₄` and the base case is immediate — the process cannot
     strip past it.
3. **Otherwise every degree is `≥ 3`,** so exercise 8.3.1 applies directly: its
   filtered set is empty, so certainly of size `≤ 1`, and its carrier hypothesis
   `4 ≤ card V` is this theorem's own `hv`.

**Reading.**  Enough edges relative to vertices force the graph to be locally rich
enough to contain four branch vertices and six connecting paths.  The invariant in
step 2 is the whole trick: deleting a low-degree vertex is "free" with respect to
the quantity `2ν - ε`, so the stripping can be run to completion without ever
losing the hypothesis.  Part (b) shows `2ν - 2` is exactly the right threshold.

**Formalisation.**  Restated additively as `2ν ≤ ε + 2` rather than `ε ≥ 2ν - 2`, to
keep ℕ-subtraction out.  Step 2's bookkeeping is the ℕ-arithmetic core and is worth
isolating: `(G.induce {v}ᶜ).edgeFinset.card + G.degree v = G.edgeFinset.card`. -/
theorem hasK4Subdivision_of_card_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hv : 4 ≤ Fintype.card V) (he : 2 * Fintype.card V ≤ G.edgeFinset.card + 2) :
    G.HasK4Subdivision := by
  sorry

/-! ## §8.4 — the chromatic polynomial `π_k` (deletion–contraction) -/

-- Thm 8.6 (deletion–contraction), stated additively: π_k(G) + π_k(G·e) = π_k(G−e)
/-- **Theorem 8.6** (deletion–contraction).  *If `G` is simple, then
`π_k(G) = π_k(G - e) - π_k(G · e)` for any edge `e` of `G`.*

**Book proof** (B&M §8.4, verbatim).  *Let `u` and `v` be the ends of `e`.  To each
`k`-colouring of `G-e` that assigns the same colour to `u` and `v`, there
corresponds a `k`-colouring of `G · e` in which the vertex of `G · e` formed by
identifying `u` and `v` is assigned the common colour of `u` and `v`.  This
correspondence is clearly a bijection (see figure 8.8).  Therefore `π_k(G · e)` is
precisely the number of `k`-colourings of `G-e` in which `u` and `v` are assigned
the same colour.*

*Also, since each `k`-colouring of `G-e` that assigns different colours to `u` and
`v` is a `k`-colouring of `G`, and conversely, `π_k(G)` is the number of
`k`-colourings of `G-e` in which `u` and `v` are assigned different colours.  It
follows that `π_k(G-e) = π_k(G) + π_k(G · e)`.*

**Skeleton** (for `π_k(G) + π_k(G · e) = π_k(G - e)` — note this is the book's own
last line, not a rearrangement of it).
1. **Split the domain.**  Build the equivalence
   `(G \ edge u v).Coloring (Fin k) ≃ {c // c u = c v} ⊕ {c // c u ≠ c v}`,
   by `decide`-ing on `c u = c v`.  Taking `Nat.card` turns the goal into a sum.
2. **Same-colour part `≃` colourings of `G · e`.**  Forwards: given `c` with
   `c u = c v`, define a colouring of `contractEdge u v` (carrier `{x // x ≠ v}`)
   by `x ↦ c x.val`.  Properness needs the case analysis in `contractEdge`'s `Adj`:
   a genuine `G`-edge is handled by `c`, and an edge arising from `v`'s incidences
   re-pointed at `u` is handled by `c u = c v`.  Backwards: given `d`, extend by
   `v ↦ d ⟨u, _⟩`.  Check the two round trips.
3. **Different-colour part `≃` colourings of `G`.**  `G` and `G \ edge u v` differ
   only in the pair `uv`, so a colouring of the latter with `c u ≠ c v` is
   literally a colouring of the former, and conversely (`h : G.Adj u v` makes
   `c u ≠ c v` automatic for colourings of `G`).
4. Rewrite step 1 by steps 2 and 3.

**Reading.**  Classify the `k`-colourings of `G - e` by whether they give `u` and
`v` the same colour: the "same" ones are the colourings of `G · e`, the "different"
ones are the colourings of `G`.  The book notes the recursion *bears a close
resemblance to the recursion formula for `τ(G)`* in theorem 2.8, and that it can be
run in either direction — reducing to empty graphs (efficient for sparse `G`) or to
complete graphs (efficient for dense `G`), as illustrated in figure 8.9.

**Formalisation.**  Stated additively, `π_k(G) + π_k(G·e) = π_k(G-e)`, to stay in
`ℕ` — the book's headline form has a subtraction.  Happily this *is* how B&M's own
proof ends, so the Lean statement is the more faithful of the two.  Steps 2 and 3
are the only real work; step 1 is bookkeeping and step 4 is `rw`. -/
theorem numColorings_add_contract
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {u v : V} (h : G.Adj u v) (k : ℕ) :
    G.numColorings k + (G.contractEdge u v).numColorings k
      = (G \ SimpleGraph.edge u v).numColorings k := by
  sorry

-- Cor 8.6: π_k(G) is a polynomial of degree ν, leading term k^ν, constant term 0, alternating signs.
-- ⚠ `[Nonempty V]` is load-bearing — the corollary is FALSE for ν = 0.
/-- **Corollary 8.6.**  *For any graph `G`, `π_k(G)` is a polynomial in `k` of degree
`ν`, with integer coefficients, leading term `k^ν` and constant term zero.
Furthermore, the coefficients of `π_k(G)` alternate in sign.*

**Book proof** (B&M §8.4, verbatim).  *By induction on `ε`.  We may assume, without
loss of generality, that `G` is simple.  If `ε = 0` then, as has already been
noted, `π_k(G) = k^ν`, which trivially satisfies the conditions of the corollary.
Suppose, now, that the corollary holds for all graphs with fewer than `m` edges,
and let `G` be a graph with `m` edges, where `m ≥ 1`.  Let `e` be any edge of `G`.
Then both `G - e` and `G · e` have `m - 1` edges, and it follows from the induction
hypothesis that there are non-negative integers `a₁, …, a_{ν-1}` and
`b₁, …, b_{ν-2}` such that*

    π_k(G - e) = ∑_{i=1}^{ν-1} (-1)^{ν-i} aᵢ kⁱ + k^ν
    π_k(G · e) = ∑_{i=1}^{ν-2} (-1)^{ν-i-1} bᵢ kⁱ + k^{ν-1}

*By theorem 8.6*

    π_k(G) = π_k(G - e) - π_k(G · e)
           = ∑_{i=1}^{ν-2} (-1)^{ν-i}(aᵢ + bᵢ)kⁱ - (a_{ν-1} + 1)k^{ν-1} + k^ν

*Thus `G`, too, satisfies the conditions of the corollary.  The result follows by
the principle of induction.*

**Skeleton** (for the five-fold `∃ p : Polynomial ℤ, …`).
1. **Strong induction on `G.edgeFinset.card`.**
2. **Base `ε = 0`.**  Then `G = ⊥` and `π_k(G) = k^ν`, so take `p = X^ν`.  The five
   conjuncts: evaluation is `pow`; `natDegree = ν`; `leadingCoeff = 1`;
   `coeff 0 = 0` (here `[Nonempty V]` is needed — for `ν = 0`, `X^0 = 1` has
   constant term `1`); alternation holds since every other coefficient is `0`.
3. **Step.**  Pick an edge `uv`.  Both `G \ edge u v` (on the same carrier, `ν`
   vertices) and `G.contractEdge u v` (carrier `{x // x ≠ v}`, `ν - 1` vertices)
   have fewer edges; the induction hypothesis gives `p₁` and `p₂` of degrees `ν`
   and `ν - 1`.
4. Theorem 8.6 (rearranged) gives `π_k(G) = π_k(G-e) - π_k(G·e)`, so set
   `p = p₁ - p₂` and get the evaluation conjunct from `hp₁`, `hp₂` and the ℤ-cast
   of the ℕ-subtraction (valid since `π_k(G·e) ≤ π_k(G-e)`).
5. **The four shape conjuncts** follow the book's displayed computation:
   `natDegree` and `leadingCoeff` survive because `deg p₂ = ν - 1 < ν = deg p₁`;
   `coeff 0 = 0` because both constant terms vanish; and the **alternation adds
   rather than cancels** because `p₂`'s sign pattern is `(-1)^{(ν-1)-i}`, which the
   subtraction flips to `(-1)^{ν-i}` — this is exactly the book's
   `(-1)^{ν-i}(aᵢ + bᵢ)` line, and is the one step worth doing slowly.

**Reading.**  This is what justifies calling `π_k(G)` the **chromatic polynomial**.
The book notes that *no one has yet discovered which polynomials are chromatic*:
Read (1968) conjectured the coefficients must first rise then fall in absolute
value, but even that plus this corollary is not sufficient — `k⁴ - 3k³ + 3k²`
satisfies all of them yet is no graph's chromatic polynomial (exercise 8.4.2(b)).

**Formalisation.**  `[Nonempty V]` is load-bearing, as step 2 shows: for `ν = 0` the
empty graph has `π_k = 1`, whose constant term is `1`, not `0`.  The alternation is
encoded as `∀ i, 0 ≤ (-1)^(ν - i) * p.coeff i` rather than as an explicit sum with
non-negative `aᵢ`, which is equivalent and much easier to carry through step 5. -/
theorem exists_chromaticPolynomial
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) :
    ∃ p : Polynomial ℤ,
      (∀ k : ℕ, p.eval (k : ℤ) = (G.numColorings k : ℤ)) ∧
      p.natDegree = Fintype.card V ∧
      p.leadingCoeff = 1 ∧
      p.coeff 0 = 0 ∧
      ∀ i, 0 ≤ (-1 : ℤ) ^ (Fintype.card V - i) * p.coeff i := by
  sorry

-- Ex 8.4.2(a): the coefficient of k^{ν−1} in π_k(G) is −ε
/-- **Exercise 8.4.2(a)** (B&M §8.4, verbatim).  *Show, by means of theorem 8.6, that
if `G` is simple, then the coefficient of `k^{ν-1}` in `π_k(G)` is `-ε`.*

**Book proof.**  None — an exercise; "by means of theorem 8.6" is the whole hint.

**Skeleton** (for `p.coeff (ν - 1) = -(ε : ℤ)`, given `hp : ∀ k, p.eval k = π_k(G)`).
1. **Uniqueness first.**  `hp` pins `p` down: two integer polynomials agreeing at
   every natural number are equal (their difference has infinitely many roots).
   So `p` may be replaced by the polynomial produced by corollary 8.6, and the
   induction there re-used.
2. **Induct on `ε`.**
3. **Base `ε = 0`.**  `p = X^ν`, whose `ν - 1` coefficient is `0`, matching
   `-(0 : ℤ)`.
4. **Step.**  With `p = p₁ - p₂` as in corollary 8.6 step 4: `p₁` belongs to
   `G - e`, which has `ε - 1` edges, so the induction hypothesis gives
   `p₁.coeff (ν-1) = -(ε - 1)`.  And `p₂` belongs to `G · e`, of degree exactly
   `ν - 1` with leading coefficient `1`, so `p₂.coeff (ν-1) = 1`.  Hence
   `p.coeff (ν-1) = -(ε-1) - 1 = -ε`.

**Reading.**  The second coefficient of the chromatic polynomial simply counts the
edges.  The mechanism is that each deletion–contraction step peels off exactly one
copy of the contracted graph's leading term, and the contracted graph has degree
one less — so the `k^{ν-1}` coefficient decrements once per edge.  This is a first
small step toward the general question of which polynomials are chromatic, and it
is what makes exercise 8.4.2(b) possible.

**Formalisation.**  `p` is a hypothesis rather than a construction, which is why
step 1 is needed at all — without uniqueness there is no link between the `p` given
here and the one corollary 8.6 builds.  That uniqueness lemma is worth stating once
and reusing in exercises 8.4.2(b) and 8.4.8. -/
theorem chromaticPolynomial_coeff_card_sub_one {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : Polynomial ℤ}
    (hp : ∀ k : ℕ, p.eval (k : ℤ) = (G.numColorings k : ℤ)) :
    p.coeff (Fintype.card V - 1) = -(G.edgeFinset.card : ℤ) := by
  sorry

-- Ex 8.4.3(a): if G is a tree, π_k(G) = k(k−1)^{ν−1}
/-- **Exercise 8.4.3(a)** (B&M §8.4, verbatim).  *Show that if `G` is a tree, then
`π_k(G) = k(k-1)^{ν-1}`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `π_k(G) = k * (k-1)^(ν-1)`).  Induct on `ν`; the leaf-peeling
argument is shorter here than deletion–contraction.
1. **Base `ν = 1`.**  A one-vertex tree has exactly `k` colourings.
2. **Step.**  A tree with `ν ≥ 2` has a leaf `v` (Mathlib: `IsTree` gives an
   `exists_leaf`-style lemma; otherwise a minimum-degree vertex of an acyclic
   connected graph).  Let `w` be its unique neighbour.
3. `G.induce {v}ᶜ` is again a tree, on `ν - 1` vertices, so the induction
   hypothesis gives it `k(k-1)^{ν-2}` colourings.
4. **The fibre count.**  Restriction along `{v}ᶜ ↪ V` is a `(k-1)`-to-one map on
   colourings: each colouring of `G - v` extends to `v` in exactly `k - 1` ways
   (any colour but `c w`, `w` being `v`'s only neighbour).  Formalise as an
   equivalence `G.Coloring (Fin k) ≃ (G - v).Coloring (Fin k) × {j // j ≠ c w}` or
   as a `Finset.card_eq_of_...` fibre argument.
5. Multiply: `(k-1) · k(k-1)^{ν-2} = k(k-1)^{ν-1}`.

**Reading.**  Root the tree anywhere and colour outward: the root takes any of the
`k` colours, and every other vertex is reached across exactly one edge from its
already-coloured parent, so it avoids just that one colour.  The formula reflects
the structure exactly — `ν - 1` edges, each imposing precisely one constraint, with
no cycles to make the constraints interact.

**Formalisation.**  `(k - 1)` is ℕ-subtraction, harmless because at `k = 0` both
sides are `0` for a nonempty tree.  Consumed by exercises 8.4.3(b) (as the spanning
tree bound) and 8.4.4 (as the deleted-edge case of the cycle). -/
theorem numColorings_of_isTree {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} (h : G.IsTree) (k : ℕ) :
    G.numColorings k = k * (k - 1) ^ (Fintype.card V - 1) := by
  sorry

-- Ex 8.4.3(b): connected ⇒ π_k ≤ k(k−1)^{ν−1}, with equality iff tree (for k ≥ 2)
/-- **Exercise 8.4.3(b)** (B&M §8.4, verbatim).  *Deduce that if `G` is connected,
then `π_k(G) ≤ k(k-1)^{ν-1}`, and show that equality holds only when `G` is a
tree.*

**Book proof.**  None — an exercise; "deduce" points at part (a).

**⚠ Statement repaired — deviates from the book.**  Read per-`k`, the equality clause
is **false** at `k = 2`: take `G = C₄`, which is connected and not a tree, yet
`π₂(C₄) = 2` (two alternating 2-colourings) and `k(k-1)^{ν-1} = 2 · 1³ = 2`.
Equality holds; `IsTree` fails.  The guard has therefore been **strengthened** from
`2 ≤ k` to `3 ≤ k`, under which the argument below works.  (B&M's own phrasing is
probably best read as equality *of the polynomials* — `(∀ k, π_k(G) = k(k-1)^{ν-1})
↔ G.IsTree` — which is also true and would be an equally good repair; the `3 ≤ k`
form was chosen as the smaller change to the existing statement.)  Either way this
is a deliberate divergence from B&M, recorded here so it is not mistaken for a
transcription slip.

**Skeleton.**
*The inequality (unconditional in `k`).*
1. A connected graph has a spanning tree `T` (corollary 2.4.1), with `T ≤ G` and
   the same vertex set.
2. Every proper colouring of `G` is a proper colouring of `T` — extra edges only
   add constraints — and this inclusion of colouring-types is injective.  So
   `π_k(G) ≤ π_k(T)`.
3. Part (a) evaluates `π_k(T) = k(k-1)^{ν-1}`.

*The equality clause (under the statement's `3 ≤ k` guard).*
4. (←) If `G` is a tree it is its own spanning tree; apply (a).
5. (→) Contrapositive.  If `G` is not a tree it has an edge `xy` outside `T`.
   Exhibit a proper `k`-colouring of `T` that is **not** proper for `G`: one with
   `c x = c y`.  Construct it by 3-colouring the `T`-path from `x` to `y` with
   matching endpoints — possible for any path length once `k ≥ 3`, and *impossible*
   at `k = 2` when the path has odd length, which is exactly the `C₄`
   counterexample above — then extending greedily over the rest of `T`.
6. So the injection of step 2 misses a colouring, making the inequality strict.

**Reading.**  Among connected graphs on `ν` vertices, trees are exactly the ones
with the most colourings: every extra edge kills at least one colouring of the
spanning tree.

**Formalisation.**  The two clauses are bundled as a conjunction because the book
states them together; only the second needs the guard on `k`.  Note step 5 is where
the whole content sits — step 2's inequality is nearly formal. -/
theorem numColorings_le_of_connected {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.Connected) (k : ℕ) :
    G.numColorings k ≤ k * (k - 1) ^ (Fintype.card V - 1) ∧
      (3 ≤ k → (G.numColorings k = k * (k - 1) ^ (Fintype.card V - 1) ↔ G.IsTree)) := by
  sorry

-- Ex 8.4.4: if G is a cycle of length n, π_k(G) = (k−1)ⁿ + (−1)ⁿ(k−1)  (over ℤ)
/-- **Exercise 8.4.4** (B&M §8.4, verbatim).  *Show that if `G` is a cycle of length
`n`, then `π_k(G) = (k-1)ⁿ + (-1)ⁿ(k-1)`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `π_k(C_n) = (k-1)ⁿ + (-1)ⁿ(k-1)` over `ℤ`).  Induct on `n` via
deletion–contraction.
1. **Base `n = 3`.**  `π_k(C₃) = π_k(K₃) = k(k-1)(k-2)`, and
   `(k-1)³ - (k-1) = (k-1)((k-1)² - 1) = (k-1)(k² - 2k) = k(k-1)(k-2)`.  ✓
2. **Step, `n ≥ 4`.**  Pick any edge `e` of `C_n`.
   * `C_n - e` is the path on `n` vertices — a tree — so exercise 8.4.3(a) gives
     `π_k = k(k-1)^{n-1}`.
   * `C_n · e` is `C_{n-1}`; this needs an explicit isomorphism, since
     `contractEdge` produces a graph on `{x // x ≠ v}` rather than on `Fin (n-1)`.
3. Theorem 8.6 then reads `π_k(C_n) = k(k-1)^{n-1} - π_k(C_{n-1})`.
4. Substitute the induction hypothesis and simplify over `ℤ`:

       k(k-1)^{n-1} - [(k-1)^{n-1} + (-1)^{n-1}(k-1)]
         = (k-1)^{n-1}(k - 1) + (-1)^n (k-1)
         = (k-1)^n + (-1)^n (k-1)   ✓

   `ring` should close this once the `(-1)^{n-1} = -(-1)^n` rewrite is supplied.

**Reading.**  Sanity checks: at `k = 2` the formula gives `1 + (-1)ⁿ`, which is `2`
for even `n` and `0` for odd `n` — matching that even cycles are bipartite (two
2-colourings) and odd cycles are not (none).  The `(-1)ⁿ` term is precisely where
the parity of the cycle enters, and it is what makes odd cycles the exceptional
family throughout this chapter.

**Formalisation.**  Stated over `ℤ` with a cast on the left, because
`(k-1)ⁿ + (-1)ⁿ(k-1)` is not a natural number expression — the `(-1)ⁿ` term is
genuinely negative for odd `n`.  The base case is `n = 3` rather than `n = 0`
because `cycleGraph n` is only a cycle for `n ≥ 3`, and because contracting an edge
of `C₃` would leave a multi-edge, which `contractEdge` silently simplifies. -/
theorem numColorings_cycleGraph (n k : ℕ) (hn : 3 ≤ n) :
    ((cycleGraph n).numColorings k : ℤ)
      = ((k : ℤ) - 1)^n + (-1)^n * ((k : ℤ) - 1) := by
  sorry

-- Ex 8.4.5(a): π_k(G ∨ K₁) = k · π_{k−1}(G)  (`1 ≤ k` load-bearing)
/-- **Exercise 8.4.5(a)** (B&M §8.4, verbatim).  *Show that `π_k(G ∨ K₁) = kπ_{k-1}(G)`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `π_k(G.join ⊤) = k * π_{k-1}(G)`, `⊤ : SimpleGraph Unit`).
1. The apex is adjacent to *every* vertex of `G`, so in any colouring of the join
   no vertex of `G` shares the apex's colour.
2. Build the equivalence

       (G.join ⊤).Coloring (Fin k) ≃ Σ j : Fin k, G.Coloring {c : Fin k // c ≠ j}

   sending `c` to `⟨c apex, restriction of c to G⟩`.  Well-defined by step 1;
   inverse assembles a colouring from an apex colour and a colouring avoiding it.
3. For each `j`, `{c : Fin k // c ≠ j} ≃ Fin (k-1)`, so each summand has
   `π_{k-1}(G)` elements.
4. `Nat.card` of a `Σ` over `Fin k` with constant fibres is `k *` the fibre size.

**Reading.**  Choose the apex's colour first — `k` ways — and then `G` must be
coloured with the remaining `k - 1` colours.  This is the chromatic-polynomial
counterpart of `χ(G ∨ K₁) = χ(G) + 1`, the `K₁` case of exercise 8.1.10(a).

**Formalisation.**  `hk : 1 ≤ k` keeps `k - 1` from truncating in step 3, where the
equivalence `{c : Fin k // c ≠ j} ≃ Fin (k-1)` genuinely needs `k ≥ 1`.  The
*statement* happens to hold at `k = 0` as well — both sides are then `0`, the join
being nonempty — so `hk` is a convenience for the proof rather than a correction to
the claim. -/
theorem numColorings_join_singleton {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    (k : ℕ) (hk : 1 ≤ k) :
    (G.join (⊤ : SimpleGraph Unit)).numColorings k = k * G.numColorings (k - 1) := by
  sorry

-- Ex 8.4.5(b): if G is a wheel with n spokes, π_k(G) = k(k−2)ⁿ + (−1)ⁿk(k−2)  (over ℤ)
/-- **Exercise 8.4.5(b)** (B&M §8.4, verbatim).  *Using (a) and exercise 8.4.4, show
that if `G` is a wheel with `n` spokes, then `π_k(G) = k(k-2)ⁿ + (-1)ⁿ k(k-2)`.*

**Book proof.**  None — an exercise, but the book names both ingredients.

**Skeleton** (for `π_k(wheel n) = k(k-2)ⁿ + (-1)ⁿ k(k-2)` over `ℤ`).  Pure
substitution — no new graph theory.
1. `wheel n` is by definition `(cycleGraph n).join ⊤`, so part (a) applies:
   `π_k(wheel n) = k * π_{k-1}(cycleGraph n)`.
2. Exercise 8.4.4 at `k - 1`:
   `π_{k-1}(C_n) = ((k-1) - 1)ⁿ + (-1)ⁿ((k-1) - 1) = (k-2)ⁿ + (-1)ⁿ(k-2)`.
3. Multiply by `k` and `ring`.
4. **The cast is the real work.**  Step 1 lives in `ℕ` with `k - 1` truncating;
   step 2's statement is over `ℤ` in the variable `k`.  Instantiating 8.4.4 at the
   *natural* `k - 1` and then pushing to `ℤ` requires `1 ≤ k` to know
   `((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1`.  Do this rewrite explicitly before `ring`.

**Reading.**  A wheel with `n` spokes is `C_n ∨ K₁` — a rim cycle plus a hub joined
to every rim vertex — so its colourings are a hub colour together with a colouring
of the rim in the remaining palette.  Sanity check: at `k = 3` and odd `n` the
formula gives `3·1 + (-1)·3·1 = 0`, matching that a wheel with an odd rim is
4-chromatic and so has no 3-colouring at all.

**Formalisation.**  `hn : 3 ≤ n` is inherited from exercise 8.4.4 (the rim must be a
genuine cycle); `hk : 1 ≤ k` is what step 4 consumes. -/
theorem numColorings_wheel (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k) :
    ((wheel n).numColorings k : ℤ)
      = (k : ℤ) * ((k : ℤ) - 2)^n + (-1)^n * (k : ℤ) * ((k : ℤ) - 2) := by
  sorry

-- Ex 8.4.6: components multiply — π_k(G) = ∏ over components
/-- **Exercise 8.4.6** (B&M §8.4, verbatim).  *Show that if `G₁, G₂, …, G_ω` are the
components of `G`, then `π_k(G) = π_k(G₁)π_k(G₂)…π_k(G_ω)`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `π_k(G) = ∏ c : G.ConnectedComponent, π_k(G.induce c.supp)`).
1. **The one fact needed:** both ends of any edge lie in the same connected
   component (`ConnectedComponent.eq_of_adj` or similar).
2. Build the equivalence

       G.Coloring (Fin k) ≃ Π c : G.ConnectedComponent, (G.induce c.supp).Coloring (Fin k)

   Forwards: restrict.  Backwards: given a family, colour `v` by the component
   colouring at `v`'s own component; properness is step 1.  The round trips are
   definitional once the `ConnectedComponent.lift` is set up.
3. `Nat.card` of a `Π` over a `Fintype` is the product of the fibre cardinalities.

**Reading.**  No edge joins different components, so their colourings are entirely
independent: a colouring of `G` is precisely a choice of colouring for each
component, and the count multiplies.  This is the chromatic-polynomial version of
`χ(G) = max χ(Gᵢ)`, and one of the formulae the book lists as *facilitating the
calculation of chromatic polynomials*.

**Formalisation.**  Step 2 is the same "components are independent" equivalence used
by `IsCritical.connected` (in its `sup` form) — worth building once in a shared
place and specialising twice, since the counting and the `χ` versions differ only
in what is applied to the resulting family. -/
theorem numColorings_eq_prod_components {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    G.numColorings k = ∏ c : G.ConnectedComponent, (G.induce c.supp).numColorings k := by
  sorry

-- Ex 8.4.7: G ∩ H complete ⇒ π_k(G∪H)·π_k(G∩H) = π_k(G)·π_k(H)  (must use the Subgraph lattice)
/-- **Exercise 8.4.7** (B&M §8.4, verbatim).  *Show that if `G ∩ H` is complete, then
`π_k(G ∪ H)π_k(G ∩ H) = π_k(G)π_k(H)`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `π_k(G' ⊔ H') * π_k(G' ⊓ H') = π_k(G') * π_k(H')`).
1. **Degenerate case first.**  If `k < |(G' ⊓ H').verts|` the overlap has no
   colouring, so `π_k(G' ⊓ H') = 0`, and also `π_k(G') = 0` (its restriction would
   colour the overlap).  Both sides vanish; dispatch and assume from now on that
   the overlap is colourable.
2. **Colourings of a union are agreeing pairs.**  Every edge of `G' ⊔ H'` lies in
   `G'` or in `H'`, so restriction gives an equivalence

       (G' ⊔ H').Coloring (Fin k) ≃ {p : G'.Coloring _ × H'.Coloring _ // p.1, p.2 agree on (G' ⊓ H').verts}

3. **Fibres of restriction are equinumerous** — this is where completeness of the
   overlap is spent.  Any colouring of a complete graph is injective, and any two
   injections differ by a permutation of `Fin k`; permuting colours is a bijection
   of `G'.Coloring (Fin k)`.  Hence the restriction map
   `G'.Coloring _ → (G' ⊓ H').Coloring _` has all fibres of one common size `f_G`,
   giving `π_k(G') = π_k(G' ⊓ H') * f_G`.  Likewise `π_k(H') = π_k(G' ⊓ H') * f_H`.
4. Count step 2 by summing over the overlap colouring `d`:
   `π_k(G' ⊔ H') = Σ_d f_G · f_H = π_k(G' ⊓ H') · f_G · f_H`.
5. Multiply step 4 by `π_k(G' ⊓ H')` and compare with step 3 — the identity, with
   no division anywhere.

**Reading.**  A gluing formula.  A colouring of the union is a pair of colourings of
the parts agreeing on the overlap; because the overlap is *complete*, its vertices
must take distinct colours, which makes the two sides' colourings matchable in a
uniform number of ways.  Together with exercise 8.4.6 (components multiply) this is
one of the practical tools for computing chromatic polynomials by decomposition.

**Formalisation.**  Phrased on the `Subgraph` lattice — `⊔` and `⊓` of `G.Subgraph`
— because `SimpleGraph V` has no notion of union/intersection with differing vertex
sets.  `hcomp : (G' ⊓ H').coe = ⊤` says the overlap is complete *as a graph on its
own vertex set*.  Note that the book's identity is stated multiplicatively precisely
to avoid the division that step 5 also avoids. -/
theorem numColorings_union_mul_inter {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (G' H' : G.Subgraph) (hcomp : (G' ⊓ H').coe = ⊤) (k : ℕ) :
    (G' ⊔ H').coe.numColorings k * (G' ⊓ H').coe.numColorings k
      = G'.coe.numColorings k * H'.coe.numColorings k := by
  sorry

-- Ex 8.4.8* (Lovász): no real root of π_k(G) exceeds ν
/-- **Exercise 8.4.8*** (B&M §8.4, verbatim; L. Lovász).  *Show that no real root of
`π_k(G)` is greater than `ν`.*

**Book proof.**  None — an exercise, and one the book **stars**.

**Skeleton** (for `p.eval x = 0 → x ≤ ν`).  The efficient route is *not* the
alternating-sign shape of corollary 8.6 but the **falling-factorial basis**, in
which all coefficients are non-negative.
1. **Uniqueness.**  As in exercise 8.4.2(a), `hp` determines `p`.
2. **The basis identity.**  Let `aᵢ` be the number of partitions of `V` into
   exactly `i` nonempty independent sets.  Then for every natural `k`

       π_k(G) = ∑_{i=0}^{ν} aᵢ · k(k-1)⋯(k-i+1)

   — choose the partition into colour classes (`aᵢ` ways), then injectively assign
   `i` distinct colours from `k` (the falling factorial).  This is a counting
   bijection, proved directly.
3. Since both sides agree at all naturals, step 1 upgrades this to the *polynomial*
   identity `p = ∑ᵢ aᵢ · (X)(X-1)⋯(X-i+1)`.
4. **Positivity beyond `ν`.**  For real `x > ν` and any `i ≤ ν`, every factor
   `x - j` with `j < i ≤ ν < x` is strictly positive, so each falling factorial is
   `> 0`.  All `aᵢ ≥ 0`, and `a_ν = 1` (the partition into singletons — always
   independent).  Hence `p.eval x > 0`.
5. Contrapose: `p.eval x = 0` forces `x ≤ ν`.

**Reading.**  `π_k(G)` counts colourings, so it is positive at every integer
`k ≥ χ(G)`, and `χ(G) ≤ ν` always.  The exercise strengthens this from integers to
all reals: beyond `ν` the polynomial has no zero whatsoever.  The book notes that
the roots of chromatic polynomials *exhibit an unexpected regularity* for planar
graphs, citing Tutte (1970) on their connection with the golden ratio.

**Formalisation.**  Over `ℝ` here (not `ℤ` as in corollary 8.6), since the claim is
about real roots; `hp` ties `p` to the integer-valued counting function at naturals
only, which is exactly what step 1 needs.  Step 2 is the substantial piece and is of
independent interest — it is the standard proof that `π_k` is a polynomial at all,
and an alternative to corollary 8.6's induction. -/
theorem chromaticPolynomial_no_root_gt_card {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : Polynomial ℝ}
    (hp : ∀ k : ℕ, p.eval (k : ℝ) = (G.numColorings k : ℝ))
    {x : ℝ} (hx : p.eval x = 0) :
    x ≤ Fintype.card V := by
  sorry

/-! ## §8.5 — Mycielski's construction and Descartes' girth-6 graphs -/

-- Thm 8.7 (Mycielski 1955): for k > 0 there is a triangle-free k-chromatic graph  ⭐ self-contained
/-- **Theorem 8.7** (Mycielski, 1955).  *For any positive integer `k`, there exists a
`k`-chromatic graph containing no triangle.*

**Book proof** (B&M §8.5, verbatim).  *For `k = 1` and `k = 2`, the graphs `K₁` and
`K₂` have the required property.  We proceed by induction on `k`.  Suppose that we
have already constructed a triangle-free graph `G_k` with chromatic number
`k ≥ 2`.  Let the vertices of `G_k` be `v₁, v₂, …, v_n`.  Form a new graph
`G_{k+1}` from `G_k` as follows: add `n+1` new vertices `u₁, u₂, …, u_n, v`, and
then, for `1 ≤ i ≤ n`, join `uᵢ` to the neighbours of `vᵢ` and to `v`.*

*The graph `G_{k+1}` clearly has no triangles.  For, since `{u₁, u₂, …, u_n}` is an
independent set in `G_{k+1}`, no triangles can contain more than one `uᵢ`; and if
`uᵢ vⱼ v_k uᵢ` were a triangle in `G_{k+1}`, then `vᵢ vⱼ v_k vᵢ` would be a
triangle in `G_k`, contrary to assumption.*

*We now show that `G_{k+1}` is `(k+1)`-chromatic.  Note, first, that `G_{k+1}` is
certainly `(k+1)`-colourable, since any `k`-colouring of `G_k` can be extended to a
`(k+1)`-colouring of `G_{k+1}` by colouring `uᵢ` the same as `vᵢ`, `1 ≤ i ≤ n`, and
then assigning a new colour to `v`.  Therefore it remains to show that `G_{k+1}` is
not `k`-colourable.  If possible, consider a `k`-colouring of `G_{k+1}` in which,
without loss of generality, `v` is assigned colour `k`.  Clearly, no `uᵢ` can also
have colour `k`.  Now recolour each vertex `vᵢ` of colour `k` with the colour
assigned to `uᵢ`.  This results in a `(k-1)`-colouring of the `k`-chromatic graph
`G_k`.  Therefore `G_{k+1}` is indeed `(k+1)`-chromatic.  The theorem follows from
the principle of induction.*

**Skeleton** (for `∃ V, Fintype V, G, G.CliqueFree 3 ∧ χ(G) = k`).
1. **Induct on `k`.**  Bases `k = 1` (`K₁`) and `k = 2` (`K₂`): triangle-freeness is
   immediate on `≤ 2` vertices, and the chromatic numbers are `1` and `2`.
2. **Step.**  Given triangle-free `G_k` on `W` with `χ = k ≥ 2`, take
   `G_{k+1} = mycielskian G_k` on `W ⊕ W ⊕ Unit`.
3. **Triangle-free** (`CliqueFree 3`).  Case-split a putative triangle on how many
   shadows it contains: two shadows is impossible (they are pairwise nonadjacent);
   the apex is adjacent only to shadows, so a triangle through it would need two;
   and a triangle `uᵢ vⱼ v_l` projects to the triangle `vᵢ vⱼ v_l` in `G_k` (using
   `uᵢ ~ w ↔ vᵢ ~ w`), contradicting the induction hypothesis.
4. **`(k+1)`-colourable.**  Extend a `k`-colouring `c` of `G_k` by `uᵢ ↦ c vᵢ` and
   apex ↦ the fresh colour.  Properness: `uᵢ ~ w` implies `vᵢ ~ w`, so
   `c vᵢ ≠ c w`; the apex's colour is used nowhere else.
5. **Not `k`-colourable.**  Suppose `d` is a `k`-colouring; permute so that the
   apex has the last colour `j₀`.  No shadow has colour `j₀`.  Define
   `e vᵢ = if d vᵢ = j₀ then d uᵢ else d vᵢ`.  Then
   * `e` avoids `j₀` entirely (both branches do), so it uses only `k - 1` colours;
   * `e` is proper: for `vᵢ ~ vⱼ`, at most one has colour `j₀` under `d`; if
     neither, `e = d` there; if `d vᵢ = j₀`, then `e vᵢ = d uᵢ` and
     `e vⱼ = d vⱼ`, and `uᵢ ~ vⱼ` in the mycielskian (since `vᵢ ~ vⱼ`), so
     `d uᵢ ≠ d vⱼ`.
   This gives `χ(G_k) ≤ k - 1`, contradicting the induction hypothesis.
6. Steps 4 and 5 combine to `χ(G_{k+1}) = k + 1`.

**Reading.**  One might expect a graph needing many colours to contain a large
clique — after all, a clique's vertices must all differ.  This theorem says the
converse fails badly: chromatic number can be arbitrarily high with no triangle at
all.  Starting from `K₂`, the construction gives a triangle-free `k`-chromatic graph
on `3·2^{k-2} - 1` vertices — the 5-cycle for `k = 3`, the Grötzsch graph for
`k = 4`.  The book adds that Erdős (1961) proved by the probabilistic method that
for any `k, l ≥ 2` there is a graph of girth `k` and chromatic number `l`, and that
Descartes' construction (exercise 8.5.2) already achieves girth `6`.

**Formalisation.**  Self-contained: everything needed is the local `mycielskian`
def, and step 5's recolouring is the only delicate part.  The carrier is
existentially quantified, so each induction step may change it — which is exactly
what `mycielskian` does (`W ↦ W ⊕ W ⊕ Unit`).  Note the "without loss of
generality" in the book's step 5 is a genuine permutation of the palette and must
be performed explicitly. -/
theorem exists_triangleFree_chromaticNumber_eq
    (k : ℕ) (hk : 0 < k) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.CliqueFree 3 ∧ G.chromaticNumber = k := by
  sorry

-- Ex 8.5.1: each graph Gₖ in the Mycielski tower (G₂ = K₂) is k-critical
/-- **Exercise 8.5.1** (B&M §8.5, verbatim).  *Let `G₃, G₄, …` be the graphs obtained
from `G₂ = K₂`, using Mycielski's construction.  Show that each `G_k` is
`k`-critical.*

**Book proof.**  None — an exercise.

**Skeleton** (for `(mycielskiTower k).2.IsKCritical k`, `2 ≤ k`).
1. **Induct on `k` from `2`.**  Base: `G₂ = K₂` is 2-critical by exercise 8.1.7.
2. **Chromaticity** is theorem 8.7 steps 4–6, which need only `χ(G_k) = k` — reuse
   rather than repeat, ideally by extracting
   `χ(mycielskian G) = χ(G) + 1` as a standalone lemma.
3. **Criticality.**  Use the reduction recorded under theorem 8.3: for `k ≥ 2` it
   suffices to check that `G_{k+1} - e` is `k`-colourable for every *edge* `e`.
   Three edge types, from `mycielskian`'s `Adj`:
   * **original–original** `vᵢ vⱼ`.  Criticality of `G_k` gives a
     `(k-1)`-colouring `c` of `G_k - vᵢvⱼ`; extend as in theorem 8.7 step 4
     (`uᵢ ↦ c vᵢ`, apex ↦ fresh), which uses `k` colours and stays proper because
     the only edge needing `c vᵢ ≠ c vⱼ` has been deleted.
   * **shadow–original** `uᵢ vⱼ` (present because `vᵢ ~ vⱼ`).  Again use
     criticality of `G_k` at `vᵢ vⱼ`, but now assign `uᵢ` a colour differing from
     its *remaining* neighbours — the deleted edge is exactly the constraint that
     forced the clash.
   * **apex–shadow** `v uᵢ`.  Colour `G_k` with `k` colours, set `uⱼ ↦ c vⱼ` for
     `j ≠ i`, give the apex a colour, and use the freed edge to give `uᵢ` the
     apex's colour.
4. Conclude `IsKCritical (k+1)` for `mycielskian G_k`.

**Reading.**  Theorem 8.7 already shows `G_k` is `k`-chromatic; the exercise asks
for the stronger fact that it is *minimally* so — the shadows and apex are arranged
so tightly that every element of the graph is load-bearing.  So the Mycielski tower
produces not just triangle-free graphs of high chromatic number but triangle-free
*critical* ones.  For `k = 3` it gives the 5-cycle (3-critical by exercise 8.1.7)
and for `k = 4` the Grötzsch graph, which the book displays in figure 8.2 precisely
as its example of a 4-critical graph.

**Formalisation.**  `mycielskiTower` is `Sigma`-valued, so `(mycielskiTower k).2` is
the graph and `(mycielskiTower k).1` its carrier; the induction in step 1 must
therefore be stated over the `Sigma`, not over a fixed carrier.  The definitional
unfolding `mycielskiTower (k+1) = ⟨_, (mycielskiTower k).2.mycielskian⟩` is what
makes step 2 usable. -/
theorem mycielskiTower_isKCritical (k : ℕ) (hk : 2 ≤ k) :
    (mycielskiTower k).2.IsKCritical k := by
  sorry

-- Ex 8.5.2(a)* (Descartes): from a k-chromatic girth-≥6 graph, build one with χ ≥ k+1, girth ≥ 6
/-- **Exercise 8.5.2(a)*** (B&M §8.5, verbatim; B. Descartes).  *Let `G` be a
`k`-chromatic graph of girth at least six (`k ≥ 2`).  Form a new graph `H` as
follows: Take `C(kν, ν)` disjoint copies of `G` and a set `S` of `kν` new vertices,
and set up a one–one correspondence between the copies of `G` and the `ν`-element
subsets of `S`.  For each copy of `G`, join its vertices to the members of the
corresponding `ν`-element subset of `S` by a matching.  Show that `H` has chromatic
number at least `k + 1` and girth at least six.*

**Book proof.**  None — an exercise, and one the book **stars**.  Note that the
statement already *hands you the construction*; the work is entirely in verifying
its two properties.

**Skeleton** (for `∃ W, Fintype W, H, (k+1 : ℕ∞) ≤ χ(H) ∧ 6 ≤ H.girth`).
1. **Build `H`.**  Let `S := Fin (k * ν)` and let `T` range over
   `{T : Finset S // T.card = ν}`.  Carrier `W := (T-indexed copies of V) ⊕ S`, i.e.
   `(Σ T, V) ⊕ S`.  Adjacency: within a copy, `G`'s adjacency; plus, for each `T`,
   a fixed bijection `V ≃ T` giving the matching edges between copy `T` and `T`'s
   members.  No edges inside `S`, none between distinct copies.
2. **`χ(H) ≥ k + 1`.**  Suppose `c` is a `k`-colouring of `H`.
   * `|S| = kν` and only `k` colours, so by pigeonhole some colour `j` is taken by
     at least `ν` vertices of `S`; choose exactly `ν` of them as `T₀`.
   * Copy `T₀` is matched bijectively to `T₀`, so every vertex of that copy is
     adjacent to a `T₀`-member of colour `j`, hence avoids `j`.
   * So `c` restricted to copy `T₀` is a `(k-1)`-colouring of a graph isomorphic to
     `G`, contradicting `χ(G) = k`.
3. **`girth(H) ≥ 6`.**  Classify cycles by how many matching edges they use.
   * `0`: the cycle lies inside a single copy, so has length `≥ 6` by `hgirth`.
   * `1`: impossible — a cycle cannot use a bridge between the copies and `S` an
     odd number of times.
   * `≥ 2`: the cycle leaves a copy, passes through `S`, and returns.  Since the
     matching is a matching (each `S`-vertex has at most one neighbour in each copy)
     and distinct copies meet only through `S`, the shortest such closed walk needs
     at least three copy-vertices and three `S`-vertices — length `≥ 6`.

**Reading.**  Mycielski's construction (theorem 8.7) removes triangles but still
leaves 5-cycles.  Descartes' construction is stronger — it keeps the girth at six
or more, so the graphs have no short cycles at all, and yet the chromatic number
still climbs without bound.  Blanche Descartes (1954) gave the original recursive
construction; the book calls Mycielski's the *easier* one, which is why §8.5 proves
theorem 8.7 in the text and relegates this to a starred exercise.

**Formalisation.**  The conclusion is `≥ k + 1`, not `= k + 1`: the construction
gives a lower bound and the exercise asks only for that.  Likewise `6 ≤ girth`
rather than `= 6`.  Step 1 is most of the Lean work — the indexed family of copies
and the per-copy matching bijection have to be built explicitly, and `Fintype`
instances derived for the resulting carrier. -/
theorem descartes_construction {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) {k : ℕ} (hk : 2 ≤ k)
    (hchrom : G.chromaticNumber = k) (hgirth : 6 ≤ G.girth) :
    ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W),
      (k + 1 : ℕ∞) ≤ H.chromaticNumber ∧ 6 ≤ H.girth := by
  sorry

-- Ex 8.5.2(b): for any k ≥ 2, a graph with χ ≥ k and girth ≥ 6  (honest `≥` form; see Warning 16)
/-- **Exercise 8.5.2(b)** (B&M §8.5, verbatim; B. Descartes).  *Deduce that, for any
`k ≥ 2`, there exists a `k`-chromatic graph of girth six.*

**Book proof.**  None — an exercise; "deduce" points at part (a).

**Skeleton** (for `∃ W, Fintype W, H, (k : ℕ∞) ≤ χ(H) ∧ 6 ≤ H.girth`).
1. **Induct on `k` from `2`.**
2. **Base `k = 2`.**  `K₂` has `χ = 2` and no cycles at all, so `girth = ⊤ ≥ 6`.
3. **Step.**  Given `H` with `k ≤ χ(H)` and `6 ≤ girth(H)`, apply part (a) to `H`.
   * Part (a) wants an *exact* chromatic number, so instantiate it at
     `m := χ(H)` (finite, since the carrier is a `Fintype`) rather than at `k`.
     Note `m ≥ k ≥ 2`, so (a)'s hypothesis `2 ≤ m` holds.
   * (a) returns `H'` with `m + 1 ≤ χ(H')` and `6 ≤ girth(H')`.  Since
     `k + 1 ≤ m + 1`, this is what the induction needs.

**Reading.**  High chromatic number is compatible not merely with triangle-freeness
(theorem 8.7) but with the complete absence of short cycles.  Locally such a graph
looks like a tree — every small neighbourhood is acyclic and trivially
2-colourable — yet globally it resists any bounded number of colours.  Chromatic
number is a genuinely global invariant.

**Formalisation.**  The conclusion is the honest `≥` form (`k ≤ χ`, `6 ≤ girth`)
rather than the book's "`k`-chromatic of girth six".  Two reasons: part (a) delivers
only a lower bound on `χ`, and `girth = 6` exactly would additionally require
exhibiting a 6-cycle, which the construction does not obviously do.  Step 3's
instantiation at `m` rather than `k` is the small manoeuvre that lets the `≥`
induction feed part (a)'s `=` hypothesis. -/
theorem exists_chromaticNumber_ge_girth_six (k : ℕ) (hk : 2 ≤ k) :
    ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W),
      (k : ℕ∞) ≤ H.chromaticNumber ∧ 6 ≤ H.girth := by
  sorry

/-! ## §8.6 — a storage problem (only the canonical-colouring survivor is formalized) -/

-- Ex 8.6.3: every k-colourable graph has a canonical k-colouring  (the §8.6 survivor)
/-- **Exercise 8.6.3** (B&M §8.6, verbatim).  *Show that if `G` is
`k`-vertex-colourable, then `G` has a canonical `k`-vertex colouring.*

**Book proof.**  None — an exercise; §8.6 calls the fact *easy to see* and cites
this exercise for it.

**Skeleton** (for `∃ L : List (Set V), L.length ≤ k ∧ G.IsCanonicalColouring L`).
1. **Strengthen for the induction.**  Prove instead: *for every `t : Set V` and
   every `m`, if `G.induce t` is `m`-colourable then there is a list `L` of length
   `≤ m` whose members partition `t` and satisfy the canonical condition relative
   to `t`.*  The theorem is `t = Set.univ`, `m = k`.  Induct on `m` (equivalently
   on `t` under `⊂`, which also terminates since `V` is finite).
2. **Base `m = 0`.**  Then `t = ∅` and `L = []`.
3. **Step.**  Take a colouring of `G.induce t` with classes `V₁, …, V_m`.  Enlarge
   `V₁` to a set `W₁` that is **maximal** independent within `t` — possible by
   finiteness (repeatedly add any addable vertex; no Zorn needed).
4. Vertices absorbed into `W₁` leave their old classes; the remaining classes still
   cover `t \ W₁` and are still independent, so `G.induce (t \ W₁)` is
   `(m-1)`-colourable.
5. Apply the induction hypothesis to `t \ W₁` and `m - 1`, and return
   `L = W₁ :: (result)`.  The three conjuncts of `IsCanonicalColouring` follow:
   maximality of `L[0]` is step 3, maximality of `L[i]` for `i ≥ 1` is the
   induction hypothesis (its ambient set is exactly the complement of the earlier
   classes), coverage is step 4, and pairwise disjointness holds because each
   recursive call works inside the complement of what came before.

**Reading.**  Greedily enlarge the first colour class to a maximal independent set,
absorbing whatever later classes will give up; repeat on what remains.  Nothing is
lost: the result is canonical and uses no more colours than before.

*Why this matters (§8.6).*  The storage problem asks for the fewest warehouse
compartments so that incompatible chemicals are separated — which is the chromatic
number of the incompatibility graph.  No good algorithm is known, so the book gives
an enumerative procedure: list the minimal coverings (equivalently, by theorem 7.1,
the maximal independent sets), then search over canonical colourings.  **This
exercise is what makes that search complete** — restricting attention to canonical
colourings loses nothing.  The book's example (figure 8.11) has minimal coverings
`{a,c,e,g}`, `{b,c,d,e,g}`, `{b,d,e,f}`, `{b,c,d,f}`, hence maximal independent sets
`{b,d,f}`, `{a,f}`, `{a,c,g}`, `{a,e,g}`, and `χ = 3` via the canonical colouring
`({b,d,f}, {a,e,g}, {c})`.

**Formalisation.**  `L.length ≤ k`, not `= k`: a canonical colouring may use fewer
colours than the one it was built from, and that is precisely the point — the least
length over canonical colourings *is* `χ(G)`, which is what the §8.6 procedure
computes.  Step 1's strengthening is essential: the statement as given is not
directly inductive, because the recursive call is about a *deleted* graph. -/
theorem exists_isCanonicalColouring {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {k : ℕ} (hk : G.Colorable k) :
    ∃ L : List (Set V), L.length ≤ k ∧ G.IsCanonicalColouring L := by
  sorry

-- DROPPED (see the outline's Scaffolding audit):
--   Ex 8.4.1  — chromatic polynomials of two `[figure omitted]` graphs (unstatable).
--   Ex 8.6.1  — logical sum/product laws: absorption fails without a quotient-by-minimality;
--               supports no theorem in the chapter (OVER-ENGINEERED).
--   Ex 8.6.2  — a computation in that dropped algebra; its graph is `[figure omitted]`.
-- The greedy/sequential-colouring def is proof-only scaffolding (no ch8 *statement* mentions it),
-- so it is not scaffolded here; it belongs to the Brooks / Welsh–Powell / Szekeres–Wilf proofs.
-- Menger-style planarity notions are absent from Mathlib and (verified) needed by no ch8 item.

end SimpleGraph
