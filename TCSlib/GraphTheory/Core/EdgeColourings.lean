import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

/-!
# Bondy & Murty, *Graph Theory with Applications* — Chapter 6: Edge Colourings

Sorry-skeleton extracted from `papers/bondy-murty-ch6-edge-colourings.md`.

Every proof body is `sorry`; this file is a scaffold for sorry-driven development
(fill one stub at a time, `lake build` after each).

Key design decisions taken from the outline:
* **χ′ is not redefined.** `G.lineGraph.chromaticNumber : ℕ∞` *is* the edge chromatic number,
  and `G.lineGraph.Colorable k` *is* `k`-edge-colourability, definitionally
  (`lineGraph.Adj` = "distinct edges sharing an end").  No `EdgeColoring`/`edgeChromaticNumber`
  def is written.
* **B&M's "product" is `SimpleGraph.boxProd` (`□`)**, used verbatim — no `product` def.
* **The Petersen graph** lives in the repo (`Matchings/Defs.lean`).  Because the outline's
  `import TCSlib.*` lines refer to files this scaffold does not import, it is restated locally
  as an opaque stub (see `petersenGraph`).
* Several results are ⚠ **BLOCKED** (their proofs need Euler-tour existence or ch5's
  degree-≤2 decomposition, both unproved) — but their *statements* are well-typed, so they are
  included as `sorry`-stubs.
* Two exercises (`Ex 6.1.5`, `Ex 6.2.4(b)`) are ⚠ **RESTATED**: their multigraph content is lost
  under `SimpleGraph`, where they become one-line corollaries of Vizing.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Key Definitions (NEEDED-TO-STATE; all honest, static bodies) -/

/-- Colour `i` is *represented* at `v`: some edge incident with `v` has colour `i`.
A `k`-edge colouring here is a plain function `C : G.edgeSet → Fin k` — deliberately **not** proper.

## Book definition (§6.1, p. 99) — verbatim

> A $k$-*edge colouring* $\mathscr{C}$ of a loopless graph $G$ is an assignment of
> $k$ colours, $1, 2, \ldots, k$, to the edges of $G$. The colouring
> $\mathscr{C}$ is *proper* if no two adjacent edges have the same colour.

> We say that colour $i$ is *represented* at vertex $v$ if some edge incident with
> $v$ has colour $i$.

## In Lean notation

A `k`-edge colouring is a plain function `C : G.edgeSet → Fin k`, deliberately
**not** assumed proper — that is the whole point, since Lemma 6.1.2, Theorem 6.1
and Vizing's Theorem 6.2 all operate on improper colourings and repair them.

"Represented at `v`" is `∃ e, ↑e ∈ G.incidenceSet v ∧ C e = i`.

⚠ Note this file uses **two different** colouring encodings.  Here a colouring is
a raw function `G.edgeSet → Fin k`; but `IsUniquelyEdgeColourable` below and the
`edgeChromaticNumber` results use Mathlib's `G.lineGraph.Coloring (Fin k)`, which
is proper by construction.  The two are not interchangeable, and any proof
crossing between §6.1's machinery and a `χ'` statement must convert explicitly.

## Book alternative view (§6.1, p. 99) — verbatim

> Alternatively, a $k$-edge colouring can be thought of as a partition
> $(E_1, E_2, \ldots, E_k)$ of $E$ [...] A proper $k$-edge colouring is then a
> $k$-edge colouring $(E_1, E_2, \ldots, E_k)$ in which each subset $E_i$ is a
> matching.

The partition view is what makes the connection to chapter 5's 1-factorability
(exercise 5.1.5) exact: a proper `Δ`-edge colouring of a `Δ`-regular graph *is* a
1-factorisation.
-/
def IsRepresentedAt {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (C : G.edgeSet → Fin k) (i : Fin k) (v : V) : Prop :=
  ∃ e : G.edgeSet, (e : Sym2 V) ∈ G.incidenceSet v ∧ C e = i

open scoped Classical in
/-- `c(v)`: the number of distinct colours represented at `v`.

## Book definition (§6.1, p. 100) — verbatim

> Given a $k$-edge colouring $\mathscr{C}$ of $G$ we shall denote by $c(v)$ the
> number of distinct colours represented at $v$. Clearly, we always have
> $$c(v) \le d(v) \tag{6.3}$$
> Moreover, $\mathscr{C}$ is a proper $k$-edge colouring if and only if equality
> holds in (6.3) for all vertices $v$ of $G$.

## In Lean notation

`c(v)` counts the *distinct* colours on edges at `v`, as
`(univ.filter fun i => IsRepresentedAt C i v).card`.

Two edges at `v` sharing a colour drop `c(v)` below `d(v)`; the colouring is
proper exactly when `c(v) = d(v)` everywhere — that is `numColoursAt_le_degree`
and `isProper_iff_numColoursAt_eq_degree` below.

`∑_v c(v)` is the potential function the whole chapter maximises.
-/
noncomputable def numColoursAt {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (C : G.edgeSet → Fin k) (v : V) : ℕ :=
  (Finset.univ.filter fun i => IsRepresentedAt C i v).card

/-- An **optimal** `k`-edge colouring: one that cannot be improved, where an improvement strictly
increases `∑ v, c(v)`.  A static extremal condition, not a procedure.

## Book definition (§6.1, p. 100) — verbatim

> We shall call a $k$-edge colouring $\mathscr{C}'$ an *improvement* on
> $\mathscr{C}$ if
> $$\sum_{v \in V} c'(v) > \sum_{v \in V} c(v)$$
> where $c'(v)$ is the number of distinct colours represented at $v$ in the
> colouring $\mathscr{C}'$. An *optimal* $k$-edge colouring is one which cannot be
> improved.

## In Lean notation

Among all `k`-edge colourings — proper or not — prefer those spreading colours
most widely, measured by `∑_v c(v)`.  Rendered directly as
`∀ C', ∑ v, numColoursAt C' v ≤ ∑ v, numColoursAt C v`, i.e. `C` attains the
maximum.

Since `c(v) ≤ d(v)` with equality everywhere iff proper, a proper colouring is
automatically optimal.  The chapter's strategy is the converse direction: start
from an optimal colouring and show that if it were *not* proper it could be
improved after all.

⚠ Note this is a static extremal condition, not a procedure — no improvement
algorithm is defined here.  Existence of an optimal colouring (needed by
Theorem 6.1 and Vizing) follows from finiteness of the colouring space but is
**not stated as a lemma anywhere in this file**, and both proofs will need it.
-/
def IsOptimalEdgeColouring {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (C : G.edgeSet → Fin k) : Prop :=
  ∀ C' : G.edgeSet → Fin k, ∑ v, numColoursAt C' v ≤ ∑ v, numColoursAt C v

/-- `G[E_i ∪ E_j]`, the subgraph on the edges coloured `i` or `j`.

## Book usage (§6.1, p. 100)

The book writes `G[Eᵢ ∪ Eⱼ]` without a separate definition, in the statement of
Lemma 6.1.2:

> the component of $G[E_i \cup E_j]$ that contains $u$ is an odd cycle.

## In Lean notation

Erase every edge except those coloured `i` or `j`:
`fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, C ⟨e,h⟩ = i ∨ C ⟨e,h⟩ = j}`.

If the colouring is proper this leaves maximum degree `2` — a disjoint union of
paths and cycles alternating between the two colours.  Recolouring inside such a
component is the fundamental move of the chapter; Lemma 6.1.2 says the only
components resisting improvement in an *optimal* colouring are odd cycles.

⚠ The book's `G[·]` is edge-induced, so isolated vertices are irrelevant to it.
Mathlib's `fromEdgeSet` keeps the full vertex type `V`, so the resulting graph
has isolated vertices wherever neither colour appears.  This matters when
speaking of "the component containing `u`": in the Lean rendering that component
is a single vertex when `u` meets neither colour, whereas the book's `G[Eᵢ ∪ Eⱼ]`
would not contain `u` at all.
-/
noncomputable def twoColourSubgraph {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} (C : G.edgeSet → Fin k) (i j : Fin k) :
    SimpleGraph V :=
  fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, C ⟨e, h⟩ = i ∨ C ⟨e, h⟩ = j}

/-- Subdivide the edge `uv` of `G`: replace it by `u–w–v` for a fresh vertex `w`.
⚠ Carrier change to `V ⊕ Unit`.  Real body (from the outline).

## Book definition (§3.2, p. 53; used in exercise 6.2.3(b)(i)) — verbatim

> An edge $e$ is said to be *subdivided* when it is deleted and replaced by a path
> of length two connecting its ends, the internal vertex of this path being a new
> vertex.

## In Lean notation

Put a new vertex in the middle of `uv`, so one edge becomes two.  The new vertex
has degree `2`, `u` and `v` keep their degrees, and the vertex count rises by
one — which is exactly why subdividing one edge of an even-order regular graph
flips the parity and pushes `χ'` to `Δ + 1` (exercise 6.2.3(b)(i)).

⚠ Carrier changes to `V ⊕ Unit`, so results about `G` do not transfer
automatically.

⚠ A **third** `subdivide` in the repo, after `Connectivity.lean`'s (which
subdivides an arbitrary `e : Sym2 V` and is built as a raw structure) and the one
implicit in chapter 4.  This version takes `u v : V` with a proof `G.Adj u v` and
is assembled from `deleteEdges`/`sum`/`fromEdgeSet` instead.  None of the three
files import each other, so the definitions are independent.
-/
def subdivide {V : Type*} [DecidableEq V] (G : SimpleGraph V) {u v : V}
    (_h : G.Adj u v) : SimpleGraph (V ⊕ Unit) :=
  (G.deleteEdges {s(u, v)}).sum (⊥ : SimpleGraph Unit) ⊔
    fromEdgeSet {s(Sum.inl u, Sum.inr ()), s(Sum.inr (), Sum.inl v)}

/-- `G` is **uniquely `k`-edge-colourable**: any two proper `k`-edge colourings agree up to a
permutation of the colours.

## Book definition (exercise 6.2.5, p. 104) — verbatim

> **6.2.5** $G$ is called *uniquely $k$-edge-colourable* if any two proper
> $k$-edge colourings of $G$ induce the same partition of $E$.

## In Lean notation

Colours are arbitrary labels, so what a colouring really determines is the
partition into colour classes.  Unique colourability means that partition is
forced, and any two proper colourings differ only by renaming — which is what the
permutation `σ` expresses.

Proper `k`-edge colourings are rendered as `G.lineGraph.Coloring (Fin k)`, using
Mathlib's line graph: adjacent *edges* of `G` become adjacent *vertices* of
`G.lineGraph`, so a proper vertex colouring there is a proper edge colouring
here.

⚠ "Induce the same partition" and "differ by a permutation of colours" are
equivalent only when every colour is actually *used*.  If `k` exceeds the number
of classes, two colourings can induce the same partition while no single `σ`
relates them pointwise — and conversely `σ` may permute unused colours freely.
For the intended application (`k = 3`, 3-regular, so all three classes nonempty)
this is harmless, but the definition is not faithful in general.
-/
def IsUniquelyEdgeColourable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ C C' : G.lineGraph.Coloring (Fin k), ∃ σ : Equiv.Perm (Fin k), ∀ e, C' e = σ (C e)

/-- The Petersen graph.  In the repo it lives at `Matchings/Defs.lean` (the Kneser graph on
2-subsets of `Fin 5`); restated here as an opaque stub since this scaffold does not import
`TCSlib.*`.  Do **not** re-derive it — fill from the repo definition.

## Book context (exercise 6.1.2, p. 100) — verbatim

> 6.1.2 Show that the Petersen graph is 4-edge-chromatic.

The book introduces the graph itself only by figure 4.4, so there is no
definitional text to quote.

## In Lean notation

The `3`-regular graph on ten vertices, the Kneser graph on 2-subsets of a
5-element set (adjacent when disjoint).

In this chapter it is the standing witness that (6.1) can be strict for
non-bipartite graphs: `Δ = 3` but `χ' = 4`, the upper side of Vizing's dichotomy.

Equivalently, by the partition view of a proper colouring, this is exercise
5.1.5(a)(ii) — the Petersen graph is not 1-factorable.

## Status

`sorry` — an opaque constant, so `petersenGraph_edgeChromaticNumber` below is
**unprovable** as it stands, not merely unproved.

✅ **Do not re-derive it.**  `Matchings.lean` already defines the Petersen graph
properly, as the Kneser graph on `{s : Finset (Fin 5) // s.card = 2}`.  That
carrier is also the better one for this chapter, since vertex-transitivity cuts
the case analysis down.  The obstacle is purely organisational: this scaffold
does not import `TCSlib.*`.  Fixing the import (or moving the definition to a
shared file) is preferable to writing a third Petersen graph.

⚠ Note `EulerHamilton.lean` *also* declares `petersenGraph : SimpleGraph (Fin 10)
:= sorry` — so the repo currently has two identical opaque stubs and one real
definition, none of them connected.
-/
def petersenGraph : SimpleGraph (Fin 10) := sorry

/-! ## (6.1): χ′ ≥ Δ — ⭐ build first, self-contained -/

/-- (6.1): `χ′ ≥ Δ`.

## Book statement (§6.1, p. 99) — verbatim

> Clearly, in any proper edge colouring, the edges incident with any one vertex
> must be assigned different colours. It follows that
> $$\chi' \geq \Delta \tag{6.1}$$

## In Lean notation

Take `v` of maximum degree `Δ`.  All `Δ` edges at `v` are pairwise adjacent, so a
proper colouring gives them `Δ` distinct colours.

`χ'` is `G.lineGraph.chromaticNumber`, valued in `ℕ∞`, so `Δ` is cast.

This bound is half of every result in the chapter: Theorem 6.1 says bipartite
graphs attain it, Vizing says nobody exceeds it by more than one.

## Proof plan

1. Take `v` with `G.degree v = G.maxDegree` (`exists_maximal_degree_vertex`).
2. The edges at `v` — `G.incidenceFinset v`, of size `Δ` — are pairwise adjacent
   in `G.lineGraph`, so they form a clique there.
3. `SimpleGraph.IsClique.card_le_chromaticNumber` (or `cliqueNum ≤ chromaticNumber`)
   gives `Δ ≤ χ'`.

⚠ The `ℕ∞` valuation means the final step needs `Nat.cast_le` plumbing, and the
clique lemma may be stated for `Finset` cliques rather than `Set` ones — check
which Mathlib provides before committing to step 3.

## Book remark (§6.1, p. 99) — verbatim

> Referring to the example of figure 6.1, we see that inequality (6.1) may be
> strict.

## Status

`sorry`.  The file header marks it "⭐ build first, self-contained" — it is the
only §6.1 result not blocked on Euler tours, and everything else cites it.
-/
theorem maxDegree_le_edgeChromaticNumber
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree : ℕ∞) ≤ G.lineGraph.chromaticNumber := by
  sorry

/-! ## (6.3): c(v) ≤ d(v), and properness ⟺ equality -/

/-- (6.3): `c(v) ≤ d(v)`.

## Book statement (§6.1, p. 100) — verbatim

> Clearly, we always have
> $$c(v) \le d(v) \tag{6.3}$$

## In Lean notation

`c(v)` counts distinct colours on the `d(v)` edges at `v`; distinct colours
cannot outnumber the edges carrying them.  Strict exactly when two edges at `v`
repeat a colour.

## Proof plan

The colours represented at `v` are the image of `G.incidenceFinset v` under `C`,
so
`numColoursAt C v = (G.incidenceFinset v |>.image C).card ≤ (G.incidenceFinset v).card = G.degree v`
by `Finset.card_image_le` and `card_incidenceFinset_eq_degree`.

The work is rewriting `univ.filter (IsRepresentedAt C · v)` as that image, which
is a `Finset.ext` plus unfolding `IsRepresentedAt`.

## Status

`sorry`.  Genuinely short, and needed by
`isProper_iff_numColoursAt_eq_degree` and by both main theorems.
-/
theorem numColoursAt_le_degree
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (C : G.edgeSet → Fin k) (v : V) :
    numColoursAt C v ≤ G.degree v := by
  sorry

/-- (6.3): `C` is proper ⟺ equality holds in (6.3) at every vertex.

## Book statement (§6.1, p. 100) — verbatim

> Moreover, $\mathscr{C}$ is a proper $k$-edge colouring if and only if equality
> holds in (6.3) for all vertices $v$ of $G$.

## In Lean notation

Two edges are adjacent exactly when they meet at a vertex, so "no two adjacent
edges share a colour" is "at every vertex the incident edges carry distinct
colours" — i.e. `c(v) = d(v)`.

Properness is stated directly as
`∀ e₁ e₂, G.lineGraph.Adj e₁ e₂ → C e₁ ≠ C e₂` rather than by packaging `C` as a
`lineGraph.Coloring`, since `C` here is a bare function.

This equivalence is the bridge turning "make the colouring proper" into the
numerical goal "maximise `∑_v c(v)`", which is what optimality is about.

## Proof plan

(⇒) With `C` proper, `C` is injective on `G.incidenceFinset v` (two distinct
edges at `v` are `lineGraph`-adjacent), so the image has full size and
`numColoursAt_le_degree` becomes equality via `Finset.card_image_of_injOn`.

(⇐) Contrapositive: given adjacent `e₁ ≠ e₂` with `C e₁ = C e₂`, they share a
vertex `v`; then `C` is not injective on `G.incidenceFinset v`, so the image is
strictly smaller and `c(v) < d(v)`.

⚠ Extracting the shared vertex from `G.lineGraph.Adj e₁ e₂` is the fiddly step —
`lineGraph` adjacency is stated as the edge sets meeting, so recovering an actual
`v ∈ e₁ ⊓ e₂` needs `Sym2` case analysis.

## Status

`sorry`.
-/
theorem isProper_iff_numColoursAt_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (C : G.edgeSet → Fin k) :
    (∀ e₁ e₂, G.lineGraph.Adj e₁ e₂ → C e₁ ≠ C e₂) ↔ ∀ v, numColoursAt C v = G.degree v := by
  sorry

/-! ## Lemma 6.1.1: 2-edge colouring with both colours represented ⚠ BLOCKED -/

-- Thm Lem 6.1.1 ⚠ BLOCKED on Euler-tour existence; "is not an odd cycle" is a statement about `G`
-- itself (the `p.edges.toFinset = G.edgeFinset` clause is load-bearing — Warning 14).
/-- ## Book statement (§6.1, pp. 99–100) — verbatim

> *Lemma 6.1.1*  Let $G$ be a connected graph that is not an odd cycle. Then $G$
> has a 2-edge colouring in which both colours are represented at each vertex of
> degree at least two.

## Book proof (§6.1, p. 100) — verbatim

> We may clearly assume that $G$ is nontrivial. Suppose, first, that $G$ is
> eulerian. If $G$ is an even cycle, the proper 2-edge colouring of $G$ has the
> required property. Otherwise, $G$ has a vertex $v_0$ of degree at least four.
> Let $v_0 e_1 v_1 \ldots e_\varepsilon v_0$ be an Euler tour of $G$, and set
> $$E_1 = \{e_i \mid i \text{ odd}\} \quad \text{and} \quad E_2 = \{e_i \mid i \text{ even}\} \tag{6.2}$$
> Then the 2-edge colouring $(E_1, E_2)$ of $G$ has the required property, since
> each vertex of $G$ is an internal vertex of
> $v_0 e_1 v_1 \ldots e_\varepsilon v_0$.
>
> If $G$ is not eulerian, construct a new graph $G^*$ by adding a new vertex $v_0$
> and joining it to each vertex of odd degree in $G$. Clearly $G^*$ is eulerian.
> Let $v_0 e_1 v_1 \ldots e_{\varepsilon*} v_0$ be an Euler tour of $G^*$ and
> define $E_1$ and $E_2$ as in (6.2). It is then easily verified that the 2-edge
> colouring $(E_1 \cap E, E_2 \cap E)$ of $G$ has the required property.

## In Lean notation

An Euler tour threads through every vertex; alternating colours along it means
any vertex with room for two edges sees both.  Odd cycles are the sole exception,
since alternation around an odd cycle must repeat somewhere.

⚠ "is not an odd cycle" is a statement about `G` **itself**, not about containing
one.  Hence the clause `p.edges.toFinset = G.edgeFinset` in `hnotodd` is
load-bearing: it says the cycle exhausts `G`.  Dropping it would make the
hypothesis far too strong (excluding every graph with an odd cycle anywhere) and
the lemma useless for Lemma 6.1.2, which applies it to two-coloured components.

## Proof plan

1. Eulerian case: `euler_tour_iff_no_odd_degree` gives a tour `p`; colour
   `e ↦ (index of e in p.edges) % 2`.  Both colours at `v` because the tour
   enters and leaves.
2. Non-eulerian case: build `G*` on `V ⊕ Unit` joining the new vertex to every
   odd-degree vertex; all degrees even, so step 1 applies; restrict along
   `Sum.inl`.
3. Even-cycle sub-case needs separating, since there the "degree ≥ 4" vertex does
   not exist — but the alternating colouring still works.

⚠ Two obstacles beyond the Euler theorem itself.  First, "index of `e` in
`p.edges`" needs `p.edges` to be duplicate-free — true for a trail, but the
indexing function must be built.  Second, the book's `G*` construction adds one
vertex joined to *all* odd-degree vertices; in a `SimpleGraph` that is fine, but
the parity bookkeeping when restricting back needs care.

## Status

`sorry`, and **blocked on `euler_tour_iff_no_odd_degree`** from
`EulerHamilton.lean` — which is itself `sorry`, and which this file does not
import.  This is the deepest dependency in the chapter: Lemma 6.1.2, Theorem 6.1
and Vizing all sit downstream of it.
-/
theorem exists_two_edge_colouring_both_represented
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hnotodd : ¬ ∃ (u : V) (p : G.Walk u u),
      p.IsCycle ∧ Odd p.length ∧ p.edges.toFinset = G.edgeFinset) :
    ∃ C : G.edgeSet → Fin 2,
      ∀ v : V, 2 ≤ G.degree v → ∀ i : Fin 2, IsRepresentedAt C i v := by
  sorry

/-! ## Lemma 6.1.2: an optimal colouring's 2-coloured component is an odd cycle ⚠ BLOCKED -/

open scoped Classical in
-- Thm Lem 6.1.2 ⚠ BLOCKED (via Lem 6.1.1).  "`j` represented at least twice at `u`" counts EDGES
-- (Warning 12), spelled with a `2 ≤ card (filter …)`.
-- NOTE: the conclusion's "the component equals the cycle's support" is stated as a membership
-- `∀ w, w ∈ p.support ↔ w ∈ (…).supp` to avoid a `Fintype`-on-`ConnectedComponent.supp` obligation
-- (`Set.toFinset` on `supp` does not synthesize).
/-- ## Book statement (§6.1, p. 100) — verbatim

> **Lemma 6.1.2** Let $\mathscr{C} = (E_1, E_2, \ldots, E_k)$ be an optimal
> $k$-edge colouring of $G$. If there is a vertex $u$ in $G$ and colours $i$ and
> $j$ such that $i$ is not represented at $u$ and $j$ is represented at least
> twice at $u$, then the component of $G[E_i \cup E_j]$ that contains $u$ is an
> odd cycle.

## Book proof (§6.1, pp. 100–101) — verbatim

> Let $u$ be a vertex that satisfies the hypothesis of the lemma, and denote by
> $H$ the component of $G[E_i \cup E_j]$ containing $u$. Suppose that $H$ is not
> an odd cycle. Then, by lemma 6.1.1, $H$ has a 2-edge colouring in which both
> colours are represented at each vertex of degree at least two in $H$. When we
> recolour the edges of $H$ with colours $i$ and $j$ in this way, we obtain a new
> $k$-edge colouring $\mathscr{C}' = (E_1', E_2', \ldots, E_k')$ of $G$. Denoting
> by $c'(v)$ the number of distinct colours at $v$ in the colouring
> $\mathscr{C}'$, we have
> $$c'(u) = c(u) + 1$$
> since, now, both $i$ and $j$ are represented at $u$, and also
> $$c'(v) \geq c(v) \quad \text{for} \quad v \neq u$$
> Thus $\sum_{v \in V} c'(v) > \sum_{v \in V} c(v)$, contradicting the choice of
> $\mathscr{C}$. It follows that $H$ is indeed an odd cycle.

## In Lean notation

A wasted colour at `u` — one missing, another doubled — is an opportunity to
improve; the only structure blocking the repair is an odd cycle, whose
alternation cannot work out.

⚠ "represented at least twice at `u`" counts **edges**, not colours, so `hj` is
`2 ≤ (univ.filter fun e => ↑e ∈ G.incidenceSet u ∧ C e = j).card` rather than
anything phrased via `numColoursAt`.

⚠ The conclusion "the component *is* an odd cycle" is stated as: there is an odd
cycle `p` at `u` in `twoColourSubgraph C i j` whose support coincides with the
component's `supp`.  The membership form `∀ w, w ∈ p.support ↔ w ∈ (…).supp` is
used instead of a set equality to avoid a `Fintype (ConnectedComponent.supp)`
obligation that does not synthesize.

## Proof plan

1. `by_contra`: assume no such odd cycle.
2. Apply Lemma 6.1.1 to the component `H` — this needs `H` connected (true by
   construction) and not an odd cycle (step 1).
3. Recolour: define `C'` agreeing with `C` off `H`, and on `H` using the two-
   colouring from step 2 mapped to `{i, j}`.
4. `c'(u) = c(u) + 1`: both `i` and `j` now appear at `u`, where before only `j`
   did — this uses `hi` and `hj`.
5. `c'(v) ≥ c(v)` for `v ≠ u`: off `H` nothing changes; on `H`, vertices of
   degree ≥ 2 see both colours, and degree-1 vertices see at least one.
6. Sum and contradict `hC`.

## Status

`sorry`, **blocked on Lemma 6.1.1** (hence transitively on the Euler theorem).
Step 3 is also substantial in its own right: building `C'` requires deciding
membership in a connected component, which is where the `open scoped Classical`
above earns its keep.
-/
theorem isOddCycle_component_of_isOptimalEdgeColouring
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} {C : G.edgeSet → Fin k} (hC : IsOptimalEdgeColouring C)
    {u : V} {i j : Fin k}
    (hi : ¬ IsRepresentedAt C i u)
    (hj : 2 ≤ (Finset.univ.filter
      fun e : G.edgeSet => (e : Sym2 V) ∈ G.incidenceSet u ∧ C e = j).card) :
    ∃ p : (twoColourSubgraph C i j).Walk u u,
      p.IsCycle ∧ Odd p.length ∧
      ∀ w, w ∈ p.support ↔ w ∈ ((twoColourSubgraph C i j).connectedComponentMk u).supp := by
  sorry

/-! ## Theorem 6.1: König's edge-colouring theorem — bipartite ⇒ χ′ = Δ ⚠ BLOCKED -/

/-- Theorem 6.1 (König) ⚠ BLOCKED: if `G` is bipartite then `χ′ = Δ`.

## Book statement (§6.1, p. 101) — verbatim

> **Theorem 6.1** If $G$ is bipartite, then $\chi' = \Delta$.

## Book proof (§6.1, p. 101) — verbatim

> Let $G$ be a graph with $\chi' > \Delta$, let
> $\mathscr{C} = (E_1, E_2, \ldots, E_\Delta)$ be an optimal $\Delta$-edge
> colouring of $G$, and let $u$ be a vertex such that $c(u) < d(u)$. Clearly, $u$
> satisfies the hypothesis of lemma 6.1.2. Therefore $G$ contains an odd cycle and
> so is not bipartite. It follows from (6.1) that if $G$ is bipartite, then
> $\chi' = \Delta$.

## In Lean notation

Contrapositive: if `χ' > Δ`, an optimal `Δ`-colouring cannot be proper, so by
(6.3) some `u` has `c(u) < d(u)` — a colour missing while another repeats.  That
is Lemma 6.1.2's hypothesis, which forces an odd cycle, so `G` is not bipartite.

⚠ The book's "Clearly, `u` satisfies the hypothesis of lemma 6.1.2" compresses a
real step.  From `c(u) < d(u)` one gets *some* colour repeated at `u`; getting a
colour *not represented* at `u` needs the pigeonhole `c(u) < d(u) ≤ Δ` — i.e.
that only `Δ` colours are available and fewer than `d(u)` are used.  With
`d(u) ≤ Δ` this is tight and worth isolating.

⚠ The odd cycle produced by Lemma 6.1.2 lives in `twoColourSubgraph C i j`, a
*subgraph* of `G`.  Transporting it to an odd cycle of `G` (to contradict
bipartiteness) requires a walk-level map along `twoColourSubgraph ≤ G`, which is
not stated in this file.

## Proof plan

1. `le_antisymm` against `maxDegree_le_edgeChromaticNumber` for `≥`.
2. For `≤`: `by_contra`, so `χ' > Δ`.
3. Obtain an optimal `Δ`-edge colouring — ⚠ existence is unstated in this file
   (see `IsOptimalEdgeColouring`); it follows from finiteness of
   `G.edgeSet → Fin Δ`.
4. Not proper (else `χ' ≤ Δ`), so `isProper_iff_numColoursAt_eq_degree` gives `u`
   with `c(u) < d(u)`; pigeonhole for the missing/repeated colours.
5. Lemma 6.1.2 gives an odd cycle; transport to `G` and contradict `hbip` via
   `isBipartite_iff_no_odd_cycle`-style reasoning.

## Book remarks (§6.1, p. 101; §6.3, p. 105) — verbatim

> An alternative proof of theorem 6.1, using exercise 5.2.3$a$, is outlined in
> exercise 6.1.3.

> Since $G$ is bipartite, we know, by theorem 6.1, that $\chi' = \Delta$. Hence,
> if no teacher teaches for more than $p$ periods, and if no class is taught for
> more than $p$ periods, the teaching requirements can be scheduled in a
> $p$-period timetable.

The alternative route — via `exists_regular_bipartite_supergraph` and chapter 5's
`regular_bipartite_one_factorable` — avoids Lemma 6.1.1 and hence the Euler
Euler theorem entirely.  **That is likely the better path in Lean**, since it
trades a blocked dependency for one that is merely unproved.

## Status

`sorry`, blocked via Lemma 6.1.2 on the book's route.
-/
theorem edgeChromaticNumber_eq_maxDegree_of_isBipartite
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) :
    G.lineGraph.chromaticNumber = (G.maxDegree : ℕ∞) := by
  sorry

/-! ## Theorem 6.2: VIZING'S THEOREM ⭐ the chapter's hard centre ⚠ BLOCKED -/

/-- Theorem 6.2 (Vizing) ⚠ BLOCKED: if `G` is simple then `χ′ = Δ` or `χ′ = Δ+1`.

## Book statement (§6.2, p. 101) — verbatim

> **Theorem 6.2** If $G$ is simple, then either $\chi' = \Delta$ or
> $\chi' = \Delta + 1$.

## Book proof (§6.2, pp. 101–103) — verbatim

> Let $G$ be a simple graph. By virtue of (6.1) we need only show that
> $\chi' \leq \Delta + 1$. Suppose, then, that $\chi' > \Delta + 1$. Let
> $\mathscr{C} = (E_1, E_2, \ldots, E_{\Delta+1})$ be an optimal
> $(\Delta+1)$-edge colouring of $G$ and let $u$ be a vertex such that
> $c(u)<d(u)$. Then there exist colours $i_0$ and $i_1$ such that $i_0$ is not
> represented at $u$, and $i_1$ is represented at least twice at $u$. Let $uv_1$
> have colour $i_1$, as in figure 6.2$a$.
>
> Since $d(v_1)<\Delta+1$, some colour $i_2$ is not represented at $v_1$. Now
> $i_2$ must be represented at $u$ since otherwise, by recolouring $uv_1$ with
> $i_2$, we would obtain an improvement on $\mathscr{C}$. Thus some edge $uv_2$
> has colour $i_2$. Again, since $d(v_2)<\Delta+1$, some colour $i_3$ is not
> represented at $v_2$; and $i_3$ must be represented at $u$ since otherwise, by
> recolouring $uv_1$ with $i_2$ and $uv_2$ with $i_3$, we would obtain an improved
> $(\Delta+1)$-edge colouring. Thus some edge $uv_3$ has colour $i_3$. Continuing
> this procedure we construct a sequence $v_1, v_2, \ldots$ of vertices and a
> sequence $i_1, i_2, \ldots$ of colours, such that
>
> (i) $uv_j$ has colour $i_j$, and
>
> (ii) $i_{j+1}$ is not represented at $v_j$.
>
> Since the degree of $u$ is finite, there exists a smallest integer $l$ such
> that, for some $k<l$,
>
> (iii) $i_{l+1}=i_k$.
>
> We now recolour $G$ as follows. For $1 \le j \le k-1$, recolour $uv_j$ with
> colour $i_{j+1}$, yielding a new $(\Delta+1)$-edge colouring
> $\mathscr{C}' = (E_1', E_2', \ldots, E_{\Delta+1}')$ (figure 6.2$b$). Clearly
> $$c'(v) \ge c(v) \quad \text{for all} \quad v \in V$$
> and therefore $\mathscr{C}'$ is also an optimal $(\Delta+1)$-edge colouring of
> $G$. By lemma 6.1.2, the component $H'$ of $G[E_{i_0}' \cup E_{i_k}']$ that
> contains $u$ is an odd cycle.
>
> Now, in addition, recolour $uv_j$ with colour $i_{j+1}$, $k \le j \le l-1$, and
> $uv_l$ with colour $i_k$, to obtain a $(\Delta+1)$-edge colouring
> $\mathscr{C}'' = (E_1'', E_2'', \ldots, E_{\Delta+1}'')$ (figure 6.2$c$). As
> above
> $$c''(v) \ge c(v) \quad \text{for all} \quad v \in V$$
> and the component $H''$ of $G[E_{i_0}'' \cup E_{i_k}'']$ that contains $u$ is an
> odd cycle. But, since $v_k$ has degree two in $H'$, $v_k$ clearly has degree one
> in $H''$. This contradiction establishes the theorem.

## In Lean notation

By (6.1) `χ' ≥ Δ` always, so the content is that one spare colour suffices — a
tight dichotomy in which no simple graph needs `Δ + 2`.

The disjunction is stated with the two branches at different types
(`(G.maxDegree : ℕ∞)` and `(G.maxDegree + 1 : ℕ)` coerced), which is harmless but
worth matching carefully when proving.

## Proof plan

1. Reduce to `vizing_chromatic_index_le` plus (6.1), exactly as the book's first
   sentence does.
2. For the inequality: `by_contra`, take an optimal `(Δ+1)`-colouring and `u`
   with `c(u) < d(u)`.
3. **Build the fan.**  The sequences `vⱼ`, `iⱼ` are constructed by recursion with
   the invariants (i) and (ii).  In Lean this needs an explicit
   `Nat.rec`-with-choice, and termination comes from `d(u)` finite — the book's
   "since the degree of `u` is finite" is where `l` and `k` come from, via a
   pigeonhole on `Fin (Δ+1)`.
4. **First recolouring** `C'`: shift colours down the fan below `k`.  Show
   `c'(v) ≥ c(v)` pointwise, hence `C'` still optimal; apply Lemma 6.1.2.
5. **Second recolouring** `C''`: shift the whole fan.  Same argument.
6. Contradiction from `v_k`'s degree in the two odd cycles.

⚠ Step 3 is the crux and has no analogue elsewhere in the repo: it is a
dependent recursion producing *two* sequences with a shared invariant, then a
minimality extraction for `(k, l)`.  Steps 4–5 each need a recolouring
construction plus a pointwise `c` comparison, similar to Lemma 6.1.2's step 3.

## Book remarks (§6.2, p. 103) — verbatim

> Actually, Vizing proved a more general theorem than that given above, one that
> is valid for all loopless graphs. The maximum number of edges joining two
> vertices in $G$ is called the *multiplicity* of $G$, and denoted by $\mu(G)$.
> We can now state Vizing's theorem in its full generality: if $G$ is loopless,
> then $\Delta \le \chi' \le \Delta + \mu$.

> Strong as theorem 6.2 is, it leaves open one interesting question: which simple
> graphs satisfy $\chi' = \Delta$? The significance of this question will become
> apparent in chapter 9, when we study edge colourings of planar graphs.

Under `SimpleGraph` we always have `μ = 1`, which is why the simple form is the
one stated.

## Status

`sorry`, blocked on Lemma 6.1.2 and hence on the Euler theorem.  The chapter's
hard centre — even with Lemma 6.1.2 granted, step 3's fan construction is
substantial.
-/
theorem vizing_chromatic_index
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.lineGraph.chromaticNumber = (G.maxDegree : ℕ∞) ∨
      G.lineGraph.chromaticNumber = (G.maxDegree + 1 : ℕ) := by
  sorry

/-- The core content of Vizing, `χ′ ≤ Δ+1`, from which the disjunction follows via (6.1).

## Book statement (§6.2, p. 101) — verbatim

The book does not state this separately; it is the reduction opening the proof of
Theorem 6.2:

> By virtue of (6.1) we need only show that $\chi' \leq \Delta + 1$.

## In Lean notation

The half of Vizing that carries all the work.  With (6.1) supplying `χ' ≥ Δ`,
the two together pin `χ'` into `{Δ, Δ+1}`.

## Proof plan

The whole of the book's proof of Theorem 6.2 — see the full quotation and plan on
`vizing_chromatic_index` above, which is where the argument is recorded.

`vizing_chromatic_index` should then be derived *from this*, not the reverse:
`le_antisymm`-style case split on whether `χ' = Δ`, using
`maxDegree_le_edgeChromaticNumber` for the lower bound.

## Status

`sorry`.  ⚠ Note the two Vizing declarations are currently independent stubs;
the intended dependency (disjunction ⟵ inequality) is not yet expressed in the
file, so whoever proves this should also rewrite `vizing_chromatic_index` to cite
it rather than re-run the argument.
-/
theorem vizing_chromatic_index_le
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.lineGraph.chromaticNumber ≤ (G.maxDegree + 1 : ℕ) := by
  sorry

/-! ## Lemma 6.3: rebalancing two disjoint matchings ⚠ BLOCKED -/

-- Thm Lem 6.3 ⚠ BLOCKED on ch5's deg-≤2 decomposition.  `|M'| = |M| − 1` stated additively.
/-- ## Book statement (§6.3, p. 105) — verbatim

> **Lemma 6.3** Let $M$ and $N$ be disjoint matchings of $G$ with $|M| > |N|$.
> Then there are disjoint matchings $M'$ and $N'$ of $G$ such that
> $|M'| = |M| - 1$, $|N'| = |N| + 1$ and $M' \cup N' = M \cup N$.

## Book proof (§6.3, p. 105) — verbatim

> Consider the graph $H = G[M \cup N]$. As in the proof of theorem 5.1, each
> component of $H$ is either an even cycle, with edges alternately in $M$ and $N$,
> or else a path with edges alternately in $M$ and $N$. Since $|M| > |N|$, some
> path component $P$ of $H$ must start and end with edges of $M$. Let
> $P = v_0 e_1 v_1 \ldots e_{2n+1} v_{2n+1}$, and set
> $$M' = (M \backslash \{e_1, e_3, \ldots, e_{2n+1}\}) \cup \{e_2, e_4, \ldots, e_{2n}\}$$
> $$N' = (N \backslash \{e_2, e_4, \ldots, e_{2n}\}) \cup \{e_1, e_3, \ldots, e_{2n+1}\}$$
> Then $M'$ and $N'$ are matchings of $G$ that satisfy the conditions of the
> lemma.

## In Lean notation

Swapping roles along `P` moves exactly one edge from the larger matching to the
smaller, leaving the union unchanged.  Repeated application *balances* a family
of matchings — in §6.3's timetabling reading, spreading lessons evenly across
periods so fewer classrooms are needed at once.

`|M'| = |M| - 1` is stated additively as `M'.ncard + 1 = M.ncard` to avoid ℕ
subtraction.

Matchings are carried as `Set (Sym2 V)` together with an existential witness
`∃ S : G.Subgraph, S.IsMatching ∧ S.edgeSet = M`, rather than as subgraphs
directly — which makes the set operations `\`, `∪` in the book's formulas
literal, at the cost of re-deriving the subgraph witness for `M'` and `N'`.

## Proof plan

1. Form `H` on the edge set `M ∪ N`; every vertex meets at most one edge of each
   matching, so `H` has maximum degree `≤ 2`.
2. Decompose `H` into paths and even cycles.
3. `|M| > |N|` forces some path component to start and end with `M`-edges.
4. Swap along it and re-derive the two subgraph witnesses.

⚠ Step 2 is the **same degree-≤2 structure lemma that blocks
`berge_maximum_matching` in `Matchings.lean`** — the book itself says "as in the
proof of theorem 5.1".  Mathlib does not have it.  Proving it once, in a shared
place, would unblock Berge, this lemma, and Theorem 6.3 together; that is
probably the single highest-leverage missing lemma across chapters 5 and 6.

## Status

`sorry`, blocked on that structure lemma.
-/
theorem exists_rebalanced_matchings
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {M N : Set (Sym2 V)} (hM : ∃ SM : G.Subgraph, SM.IsMatching ∧ SM.edgeSet = M)
    (hN : ∃ SN : G.Subgraph, SN.IsMatching ∧ SN.edgeSet = N)
    (hdisj : Disjoint M N) (hlt : N.ncard < M.ncard) :
    ∃ M' N' : Set (Sym2 V),
      (∃ SM' : G.Subgraph, SM'.IsMatching ∧ SM'.edgeSet = M') ∧
      (∃ SN' : G.Subgraph, SN'.IsMatching ∧ SN'.edgeSet = N') ∧
      Disjoint M' N' ∧
      M'.ncard + 1 = M.ncard ∧ N'.ncard = N.ncard + 1 ∧ M' ∪ N' = M ∪ N := by
  sorry

/-! ## Theorem 6.3: p balanced matchings covering E ⚠ BLOCKED -/

-- Thm 6.3 ⚠ BLOCKED (both chains).  `{ε/p}` is the CEILING, `[ε/p]` the FLOOR (Warning 7).
/-- ## Book statement (§6.3, p. 106) — verbatim

> **Theorem 6.3** If $G$ is bipartite, and if $p \geq \Delta$, then there exist
> $p$ disjoint matchings $M_1, M_2, \ldots, M_p$ of $G$ such that
> $$E = M_1 \cup M_2 \cup \ldots \cup M_p \tag{6.4}$$
> and, for $1 \leq i \leq p$
> $$[\varepsilon/p] \leq |M_i| \leq \{\varepsilon/p\} \tag{6.5}$$
> (Note: condition (6.5) says that any two matchings $M_i$ and $M_j$ differ in
> size by at most one.)

## Book proof (§6.3, p. 106) — verbatim

> Let $G$ be a bipartite graph. By theorem 6.1, the edges of $G$ can be
> partitioned into $\Delta$ matchings $M_1', M_2', \ldots, M_\Delta'$. Therefore,
> for any $p \geq \Delta$, there exist $p$ disjoint matchings
> $M_1', M_2', \ldots, M_p'$ (with $M_i' = \emptyset$ for $i > \Delta$) such that
> $$E = M_1' \cup M_2' \cup \ldots \cup M_p'$$
> By repeatedly applying lemma 6.3 to pairs of these matchings that differ in size
> by more than one, we eventually obtain $p$ disjoint matchings
> $M_1, M_2, \ldots, M_p$ of $G$ satisfying (6.4) and (6.5), as required.

## In Lean notation

⚠ In the book's notation `[x]` is the **floor** and `{x}` the **ceiling** — the
opposite of the modern convention for `{}`.  So (6.5) reads
`⌊ε/p⌋ ≤ |Mᵢ| ≤ ⌈ε/p⌉`, rendered here as
`G.edgeFinset.card / p ≤ … ≤ (G.edgeFinset.card + p - 1) / p` in ℕ division.

⚠ The book's "repeatedly applying lemma 6.3 ... we eventually obtain" is an
induction whose **termination is not argued**.  In Lean it needs an explicit
measure — e.g. `∑ᵢ |Mᵢ|²`, which strictly decreases on each rebalancing since
moving an edge from a larger to a smaller class reduces the sum of squares.
Supplying that measure is a real part of the formalisation the book skips.

## Proof plan

1. Theorem 6.1 gives `χ' = Δ`, hence a proper `Δ`-edge colouring; its colour
   classes are `Δ` disjoint matchings covering `E`.
2. Pad with `p - Δ` empty matchings.
3. Well-founded recursion on `∑ᵢ |Mᵢ|²`: while some pair differs by `≥ 2`, apply
   `exists_rebalanced_matchings` and recurse.
4. On termination every pair differs by `≤ 1`, which with `∑ |Mᵢ| = ε` gives
   (6.5).

⚠ Step 1 needs converting a `lineGraph.Coloring` into matchings — the
partition view of §6.1 — which this file states nowhere.  That conversion is
also what exercise 5.1.5 needs, and is worth a shared lemma.

## The timetabling reading (§6.3, p. 105) — verbatim

> Suppose that altogether there are $l$ lessons to be given, and that they have
> been scheduled in a $p$-period timetable. Since this timetable requires an
> average of $l/p$ lessons to be given per period, it is clear that at least
> $\{l/p\}$ rooms will be needed in some one period. It turns out that one can
> always arrange $l$ lessons in a $p$-period timetable so that at most $\{l/p\}$
> rooms are occupied in any one period. This follows from theorem 6.3 below.

## Status

`sorry`, blocked on Theorem 6.1 and Lemma 6.3 — so transitively on both the
Euler theorem and the degree-≤2 structure lemma.
-/
theorem exists_balanced_matching_decomposition
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) {p : ℕ} (hp : G.maxDegree ≤ p) (hp0 : 0 < p) :
    ∃ M : Fin p → Set (Sym2 V),
      (∀ i, ∃ S : G.Subgraph, S.IsMatching ∧ S.edgeSet = M i) ∧
      (Pairwise fun i j => Disjoint (M i) (M j)) ∧
      (⋃ i, M i) = G.edgeSet ∧
      ∀ i, G.edgeFinset.card / p ≤ (M i).ncard ∧
           (M i).ncard ≤ (G.edgeFinset.card + p - 1) / p := by
  sorry

/-! ## Selected Exercises -/

/-- Ex 6.1.3(a): every bipartite `G` has a `Δ`-regular bipartite supergraph ⚠ carrier change.

## Book statement (§6.1, p. 100) — verbatim

> 6.1.3 ($a$) Show that if $G$ is bipartite, then $G$ has a $\Delta$-regular
> bipartite supergraph.
> &nbsp;($b$) Using ($a$) and exercise 5.2.3$a$, give an alternative proof of
> theorem 6.1.

An exercise, so the book gives no proof.

## In Lean notation

Pad until every vertex has degree exactly `Δ`.  Enlarge the smaller side with
isolated vertices so the sides match; then repeatedly join a deficient vertex on
each side — both sides have equal total deficiency, so such a pair always exists.

⚠ Carrier changes, so the statement produces a new type `W` together with an
embedding `G ↪g H`.

⚠ **The `↪g` here is a `RelEmbedding`, i.e. an *induced* embedding** — the same
trap that sank the original statement of exercise 1.4.1 in
`GraphsAndSubgraphs.lean` (recorded in
`GraphTheory/ExtractionArchive/MathlibDuplicates.md`, entry 5).
It demands `H.Adj (f a) (f b) ↔ G.Adj a b`, so the padding edges must never join
two images of `G`-vertices.  The two-disjoint-copies construction respects this;
the naive "add edges between deficient vertices of `G` itself" does **not**, and
would make the statement false.  Worth checking carefully before proving.

## Why it matters

Part (b) is the alternative proof of Theorem 6.1: a `Δ`-regular bipartite graph
is 1-factorable (exercise 5.2.3(a)), hence properly `Δ`-edge colourable, and
restricting to `G` gives `χ'(G) ≤ Δ`.

✅ **This route avoids Lemma 6.1.1 and the Euler theorem entirely**, so it is the
recommended path to Theorem 6.1 in Lean — see the note there.

## Proof plan

1. Take `W = (V ⊕ V) ⊕ (padding)`, two copies of `G` side by side.
2. Join the `i`-th copy's deficient vertices to the other copy's, which is
   legitimate for the induced-embedding condition since it never adds an edge
   within one copy.
3. Iterate on total deficiency until `Δ`-regular; bipartiteness is preserved
   throughout.

## Status

`sorry`.
-/
theorem exists_regular_bipartite_supergraph
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) :
    ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj) (_ : G ↪g H),
      H.IsBipartite ∧ H.IsRegularOfDegree G.maxDegree := by
  sorry

/-- Ex 6.1.6 (Gupta) ⚠ BLOCKED: bipartite with `δ > 0` ⇒ a `δ`-edge colouring with all colours
represented at every vertex (not required proper).

## Book statement (§6.1, p. 100) — verbatim

> 6.1.6 Show that if $G$ is bipartite with $\delta > 0$, then $G$ has a
> $\delta$-edge colouring such that all $\delta$ colours are represented at each
> vertex.
>
> (R. P. Gupta)

An exercise, so the book gives no proof.

## In Lean notation

The **dual** of proper colouring.  Proper asks that no colour appear *twice* at a
vertex, using `Δ` colours; this asks that every colour appear *at least once* at
every vertex, using `δ` colours.  Since the least degree is `δ`, that is the most
one could force everywhere.

The colouring is explicitly **not** required to be proper, so the statement is
about `IsRepresentedAt` rather than about `lineGraph.chromaticNumber` — one of
the few places the raw-function encoding is the right one.

Exercise 6.2.8 is the simple-graph analogue with `δ - 1` colours; it is not
stated in this file.

## Proof plan

The standard argument mirrors Theorem 6.1's, with the optimality potential
reversed: instead of maximising `∑_v c(v)` against `d(v)`, maximise the number of
(vertex, colour) pairs where the colour *is* represented, and use Lemma 6.1.1 to
repair any vertex missing a colour while another is doubled.

⚠ The dependent type `Fin G.minDegree` in the conclusion means the colour count
varies with `G`; any induction that changes `G` will change the target type too,
so the proof should fix `δ` as a variable up front rather than inducting on `G`
directly.

## Status

`sorry`, blocked on Lemma 6.1.1 and hence the Euler theorem.
-/
theorem exists_edge_colouring_all_represented_of_isBipartite
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) (hδ : 0 < G.minDegree) :
    ∃ C : G.edgeSet → Fin G.minDegree,
      ∀ (v : V) (i : Fin G.minDegree), IsRepresentedAt C i v := by
  sorry

/-- Ex 6.2.1*: `χ′(K_{2n−1}) = 2n−1` (explicit colouring — bypasses Vizing).

## Book statement (§6.2, p. 104) — verbatim

> **6.2.1\*** Show, by finding appropriate edge colourings, that
> $\chi'(K_{2n-1}) = \chi'(K_{2n}) = 2n - 1$.

A starred exercise, so the book gives no proof.

## In Lean notation

`K_{2n-1}` has odd order, so no colour class is a perfect matching and each
misses a vertex.  With `ε = (2n-1)(n-1)` and classes of size `≤ n - 1`, at least
`2n - 1` colours are needed — one more than `Δ = 2n - 2`.  So odd complete graphs
sit on the **upper** side of Vizing's dichotomy.

The explicit colouring: place the vertices at the corners of a regular
`(2n-1)`-gon and colour each edge by the axis of symmetry it is perpendicular to.
Each class is a matching of `n - 1` edges missing one vertex, and there are
`2n - 1` axes.

Concretely in `ZMod (2n-1)`: colour `s(a, b)` by `a + b`.  Two edges at a shared
vertex get different sums because `2` is invertible mod an odd number — which is
exactly where oddness enters.

## Proof plan

1. `≤`: the `a + b` colouring; properness from invertibility of `2` mod `2n - 1`.
2. `≥`: counting.  `Δ = 2n - 2` gives only `χ' ≥ 2n - 2` from (6.1), so the extra
   colour needs the matching bound — each class has `≤ n - 1` edges by odd order,
   and `ε = (2n-1)(n-1)`, so `χ' ≥ 2n - 1`.
3. `le_antisymm`.

⚠ Step 2 is what distinguishes this from the even case and cannot be shortcut.
Note it needs **no Vizing**, only the counting.

⚠ `2 * n - 1` truncates in ℕ at `n = 0`, which `hn` rules out.

## Status

`sorry`.  Reachable without the blocked chain, though step 2 is more work than
the even case.
-/
theorem edgeChromaticNumber_completeGraph_odd (n : ℕ) (hn : 0 < n) :
    (⊤ : SimpleGraph (Fin (2 * n - 1))).lineGraph.chromaticNumber = (2 * n - 1 : ℕ) := by
  sorry

/-- Ex 6.2.1*: `χ′(K_{2n}) = 2n−1`.

## Book statement (§6.2, p. 104) — verbatim

> **6.2.1\*** Show, by finding appropriate edge colourings, that
> $\chi'(K_{2n-1}) = \chi'(K_{2n}) = 2n - 1$.

A starred exercise, so the book gives no proof.

## In Lean notation

`K_{2n}` has `Δ = 2n - 1`, so (6.1) gives `χ' ≥ 2n - 1`.  For the upper bound use
the round-robin schedule of exercise 5.1.5(a)(i): the edges partition into
`2n - 1` perfect matchings, and colouring each with its own colour is proper.
So `χ' = Δ` and even complete graphs sit on the **lower** side of the dichotomy.

The contrast with the odd case is entirely parity: with an odd number of vertices
no round can involve everybody.

## Proof plan

1. `≥` from `maxDegree_le_edgeChromaticNumber` plus `Δ(K_{2n}) = 2n - 1`.
2. `≤` from `Matchings.lean`'s `completeGraph_even_one_factorable`: a
   1-factorisation into `2n - 1` perfect matchings *is* a proper
   `(2n-1)`-edge colouring.
3. `le_antisymm`.

⚠ Step 2 crosses files (`Matchings.lean` is not imported here) and needs the
factorisation↔colouring bridge that Theorem 6.3 and exercise 6.1.2 also want.
Alternatively, redo the centre-and-circle construction inline — the same
`ZMod (2n-1)` indexing as `completeGraph_even_one_factorable`'s plan.

## Status

`sorry`.  ✅ Together with exercise 6.1.1, one of the two results here not
blocked on the Euler/Vizing chain.
-/
theorem edgeChromaticNumber_completeGraph_even (n : ℕ) (hn : 0 < n) :
    (⊤ : SimpleGraph (Fin (2 * n))).lineGraph.chromaticNumber = (2 * n - 1 : ℕ) := by
  sorry

/-- Ex 6.2.2 ⚠ BLOCKED (Vizing): nonempty (`0 < k`) `k`-regular with `ν` odd ⇒ `χ′ = Δ+1`.

## Book statement (§6.2, p. 104) — verbatim

> **6.2.2** Show that if $G$ is a nonempty regular simple graph with $\nu$ odd,
> then $\chi' = \Delta + 1$.

An exercise, so the book gives no proof.

## In Lean notation

Each colour class is a matching, and a matching on an odd number of vertices
misses one, so has `≤ (ν-1)/2` edges.  A `k`-regular graph has `ε = kν/2`, and a
proper `k`-colouring would need `kν/2 ≤ k(ν-1)/2` — false.  So `Δ = k` colours do
not suffice, and Vizing gives exactly one more.

Generalises the odd complete graph of exercise 6.2.1: regularity plus odd order
always forces the upper class.

## Proof plan

Specialise `edgeChromaticNumber_eq_maxDegree_add_one_of_card_edges_gt` (part (a)
of 6.2.3, which is the reusable engine):
1. `Odd (card V)` gives `card V = 2n + 1`.
2. `k`-regular ⇒ `2ε = k(2n+1)`, and `Δ = k` (needs `hk : 0 < k` to rule out the
   empty graph, where `maxDegree = 0`).
3. `ε = k(2n+1)/2 > nk` — the inequality is strict exactly because `k(2n+1)` is
   odd when `k` is odd, and because `k ≥ 1`.  ⚠ This step needs care in ℕ:
   `k(2n+1)/2` truncates, so work with `2ε = k(2n+1)` throughout.
4. Apply 6.2.3(a).

## Status

`sorry`, blocked on Vizing via 6.2.3(a).
-/
theorem edgeChromaticNumber_eq_maxDegree_add_one_of_regular_odd_card
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 0 < k) (hreg : G.IsRegularOfDegree k) (hodd : Odd (Fintype.card V)) :
    G.lineGraph.chromaticNumber = (G.maxDegree + 1 : ℕ) := by
  sorry

/-- Ex 6.2.3(a) ⚠ BLOCKED (Vizing): `ν = 2n+1` and `ε > nΔ` ⇒ `χ′ = Δ+1`. Reusable.

## Book statement (§6.2, p. 104) — verbatim

> **6.2.3** (a) Let $G$ be a simple graph. Show that if $\nu = 2n + 1$ and
> $\varepsilon > n\Delta$, then $\chi' = \Delta + 1$. (V. G. Vizing)

An exercise, so the book gives no proof.

## In Lean notation

With `ν = 2n + 1` odd, every matching covers an even number of vertices so has
`≤ n` edges.  A proper `Δ`-colouring accounts for at most `nΔ` edges; `hε` says
there are more, so `Δ` colours cannot suffice and Vizing supplies exactly one
more.

✅ **The reusable engine of §6.2's exercises** — 6.2.2, 6.2.3(b)(i) and
6.2.3(b)(ii) all reduce to it.  Worth proving first among them.

## Proof plan

1. `≥ Δ` from `maxDegree_le_edgeChromaticNumber`.
2. `≠ Δ`: suppose a proper `Δ`-edge colouring exists.  Its `Δ` colour classes are
   matchings, each of size `≤ n` by the odd-order bound, so `ε ≤ nΔ` —
   contradicting `hε`.
3. Vizing pins `χ' ∈ {Δ, Δ+1}`; with step 2, `χ' = Δ + 1`.

⚠ Step 2 needs two bridges this file lacks: "colour classes of a proper colouring
are matchings" (the partition view of §6.1), and "a matching on `2n+1` vertices
has `≤ n` edges".  Both are small but neither is stated.

## Status

`sorry`, blocked on Vizing.
-/
theorem edgeChromaticNumber_eq_maxDegree_add_one_of_card_edges_gt
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (hcard : Fintype.card V = 2 * n + 1) (hε : n * G.maxDegree < G.edgeFinset.card) :
    G.lineGraph.chromaticNumber = (G.maxDegree + 1 : ℕ) := by
  sorry

/-- Ex 6.2.3(b)(i) ⚠ BLOCKED: subdividing one edge of an even-order `k`-regular graph (`k ≥ 2`)
gives `χ′ = Δ+1`.

## Book statement (§6.2, p. 104) — verbatim

> (b) Using (a), show that
> (i) if $G$ is obtained from a simple regular graph with an even number of
> vertices by subdividing one edge, then $\chi' = \Delta + 1$;
> (L. W. Beineke and R. J. Wilson)

An exercise, so the book gives no proof.

## In Lean notation

Start from `k`-regular on `2n` vertices, `ε = kn`.  Subdividing inserts a
degree-`2` vertex: `2n + 1` vertices — now odd — and `kn + 1` edges, with `Δ`
still `k` provided `k ≥ 2`.  Part (a) then applies since
`kn + 1 > kn = nΔ`.

A single subdivision flips the parity of the vertex count and pushes the graph
from the lower to the upper side of Vizing's dichotomy.

⚠ `hk : 2 ≤ k` is load-bearing: at `k = 1` the new degree-`2` vertex would
*raise* `Δ` to `2`, and the count `nΔ` would change with it, breaking the
application of part (a).

## Proof plan

1. `card (V ⊕ Unit) = 2n + 1` from `heven`.
2. `(G.subdivide huv).maxDegree = k` — the new vertex has degree `2 ≤ k`, and
   `u`, `v` keep degree `k`.
3. Edge count rises by exactly one: `ε(subdivide) = kn + 1`.
4. Apply `edgeChromaticNumber_eq_maxDegree_add_one_of_card_edges_gt`.

⚠ Steps 2–3 require degree and edge-count lemmas for `subdivide`, which this
file does not provide — the definition is stated but nothing is proved about it.
That is the bulk of the work here.

## Status

`sorry`, blocked on 6.2.3(a) and hence Vizing, plus the missing `subdivide` API.
-/
theorem edgeChromaticNumber_subdivide_eq_maxDegree_add_one
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 2 ≤ k) (hreg : G.IsRegularOfDegree k) (heven : Even (Fintype.card V))
    {u v : V} (huv : G.Adj u v) [DecidableRel (G.subdivide huv).Adj] :
    (G.subdivide huv).lineGraph.chromaticNumber = ((G.subdivide huv).maxDegree + 1 : ℕ) := by
  sorry

/-- Ex 6.2.3(b)(ii) ⚠ BLOCKED: deleting `< k/2` edges (`2 * F.card < k`) from an odd-order
`k`-regular graph gives `χ′ = Δ+1`.

## Book statement (§6.2, p. 104) — verbatim

> (ii) if $G$ is obtained from a simple $k$-regular graph with an odd number of
> vertices by deleting fewer than $k/2$ edges, then $\chi' = \Delta + 1$.
> (L. W. Beineke and R. J. Wilson)

An exercise, so the book gives no proof.

## In Lean notation

An odd-order `k`-regular graph on `2n + 1` vertices has `ε = k(2n+1)/2` and
`Δ = k`.  Deleting fewer than `k/2` edges cannot lower `Δ`, and leaves the count
above `nk`, so part (a) applies.

Odd-order regular graphs stay firmly in the upper Vizing class under small
perturbation: at least `k/2` edges must go before the conclusion can fail.

`|F| < k/2` is stated as `2 * F.card < k` to avoid ℕ division.

## Proof plan

1. `Δ(G - F) = k` — deleting `|F| < k/2` edges touches at most `2|F| < k`
   vertex-slots, so some vertex retains full degree `k`.  ⚠ This is the step the
   hypothesis is designed for and needs a counting argument, not just
   monotonicity.
2. `ε(G - F) = k(2n+1)/2 - |F| > nk`, again cleared to avoid ℕ division:
   `2ε(G-F) = k(2n+1) - 2|F| > 2nk` follows from `2|F| < k`.
3. Apply `edgeChromaticNumber_eq_maxDegree_add_one_of_card_edges_gt`.

## Status

`sorry`, blocked on 6.2.3(a) and hence Vizing.
-/
theorem edgeChromaticNumber_deleteEdges_eq_maxDegree_add_one
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 0 < k) (hreg : G.IsRegularOfDegree k) (hodd : Odd (Fintype.card V))
    (F : Finset (Sym2 V)) (hF : ↑F ⊆ G.edgeSet) (hcard : 2 * F.card < k)
    [DecidableRel (G.deleteEdges ↑F).Adj] :
    (G.deleteEdges ↑F).lineGraph.chromaticNumber =
      ((G.deleteEdges ↑F).maxDegree + 1 : ℕ) := by
  sorry

/-- Ex 6.2.5: every uniquely 3-edge-colourable 3-regular graph is hamiltonian.
⚠ `hcol` is mandatory — without it uniqueness is vacuous and the theorem is false (Warning 13).

## Book statement (§6.2, p. 104) — verbatim

> **6.2.5** $G$ is called *uniquely $k$-edge-colourable* if any two proper
> $k$-edge colourings of $G$ induce the same partition of $E$. Show that every
> uniquely 3-edge-colourable 3-regular graph is hamiltonian.
> (D. L. Greenwell and H. V. Kronk)

An exercise, so the book gives no proof.

## In Lean notation

In a cubic graph a proper 3-edge colouring splits the edges into three perfect
matchings.  Any *two* of them form a spanning 2-regular subgraph — a disjoint
union of even cycles.  If that union had more than one cycle, swapping the two
colours around a single cycle would give a genuinely different partition,
contradicting uniqueness.  So each pair of classes is a *single* spanning cycle,
i.e. a Hamilton cycle.

⚠ **`hcol` is mandatory.**  `IsUniquelyEdgeColourable` quantifies over proper
3-colourings; if none exists the condition holds **vacuously**, and the statement
would then assert that every cubic graph with no 3-edge-colouring is
hamiltonian — false, the Petersen graph being a counterexample (`χ' = 4`,
nonhamiltonian).  Requiring `G.lineGraph.Colorable 3` rules that out.

## Proof plan

1. From `hcol`, get a proper 3-colouring; its classes are three perfect
   matchings (cubic ⇒ each class saturates every vertex).
2. Take classes `1 ∪ 2`: 2-regular spanning, so a disjoint union of cycles, all
   even since they alternate.
3. Suppose two or more cycles.  Swap colours `1` and `2` on one of them; the
   result is another proper 3-colouring inducing a *different* partition, so
   `huniq` supplies a `σ` with `C' = σ ∘ C` — derive a contradiction from `σ`
   having to act differently on the swapped and unswapped cycles.
4. Hence one cycle, spanning: a Hamilton cycle.

⚠ Step 3 is where the file's permutation-based rendering of unique colourability
is actually used, and it is the step where that rendering's mismatch with "same
partition" (flagged on `IsUniquelyEdgeColourable`) could bite.  Here all three
classes are nonempty, so the two notions do agree — but the proof should make
that explicit rather than assume it.

## Status

`sorry`.
-/
theorem isHamiltonian_of_uniquely_three_edge_colourable
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3) (huniq : G.IsUniquelyEdgeColourable 3)
    (hcol : G.lineGraph.Colorable 3) :
    ∃ (u : V) (p : G.Walk u u), p.IsHamiltonianCycle := by
  sorry

/-- Ex 6.2.6(a) ⚠ BLOCKED (Vizing): `χ′(G □ K₂) = Δ(G □ K₂)`.  B&M's "product" is `boxProd`.

## Book statement (§6.2, p. 104) — verbatim

> **6.2.6** The *product* of simple graphs $G$ and $H$ is the simple graph
> $G \times H$ with vertex set $V(G) \times V(H)$, in which $(u, v)$ is adjacent
> to $(u', v')$ if and only if either $u = u'$ and $vv' \in E(H)$ or $v = v'$ and
> $uu' \in E(G)$.
>
> (a) Using Vizing's theorem (6.2), show that
> $\chi'(G \times K_2) = \Delta(G \times K_2)$.

An exercise, so the book gives no proof.

## In Lean notation

The book's "product" is exactly Mathlib's `boxProd`, written `□`.

`G □ K₂` is two disjoint copies of `G` plus a perfect matching joining
corresponding vertices, so every degree rises by one and
`Δ(G □ K₂) = Δ(G) + 1`.

Vizing gives `G` a proper `(Δ(G)+1)`-colouring.  Use it on both copies, then
colour the connecting matching edges by recycling — each vertex of a copy already
omits at least one of the `Δ(G)+1` colours, and the two copies can be arranged to
omit *different* ones, so each matching edge finds a free colour.

## Proof plan

1. `Δ(G □ K₂) = Δ(G) + 1` — a `boxProd` degree computation.
2. `≥` from `maxDegree_le_edgeChromaticNumber`.
3. `≤`: Vizing gives `C : proper (Δ+1)`-colouring of `G`.  On copy `0` use `C`;
   on copy `1` use `σ ∘ C` for a fixed cyclic shift `σ` of the colours.  For the
   matching edge at `v`, pick a colour absent at `v` in both copies — the shift
   is chosen so that such a colour exists.
4. Verify properness across the three edge kinds (within copy 0, within copy 1,
   matching edges).

⚠ Step 3's "the shift is chosen so that such a colour exists" is the delicate
part and is exactly the "careful bookkeeping" the book waves at; with `Δ+1`
colours and degree `Δ` there is at least one free colour per vertex per copy, but
making the two omissions differ needs the shift argument spelled out.

## Status

`sorry`, blocked on Vizing.
-/
theorem edgeChromaticNumber_boxProd_completeGraph_two
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (G □ (⊤ : SimpleGraph (Fin 2))).Adj] :
    (G □ (⊤ : SimpleGraph (Fin 2))).lineGraph.chromaticNumber =
      ((G □ (⊤ : SimpleGraph (Fin 2))).maxDegree : ℕ∞) := by
  sorry

/-- Ex 6.2.6(b) ⚠ BLOCKED (via (a)): if `H` is nontrivial (`0 < Δ(H)`) with `χ′(H) = Δ(H)`,
then `χ′(G □ H) = Δ(G □ H)`.

## Book statement (§6.2, p. 104) — verbatim

> (b) Deduce that if $H$ is nontrivial with $\chi'(H) = \Delta(H)$, then
> $\chi'(G \times H) = \Delta(G \times H)$.

An exercise, so the book gives no proof.

## In Lean notation

`G □ H` has degree `d(u) + d(v)` at `(u, v)`, so `Δ(G □ H) = Δ(G) + Δ(H)`.
Decompose `H` into `Δ(H)` matchings via its optimal colouring; each matching
crossed with `G` reproduces part (a)'s situation, and assembling gives
`Δ(G) + Δ(H)` colours.

So the class attaining `χ' = Δ` is closed under products with any nontrivial
member — one of the few general constructions guaranteeing the lower Vizing
class.

`H` nontrivial is `0 < H.maxDegree`; without it `H` is edgeless, `G □ H` is a
disjoint union of copies of `G`, and the claim reduces to `χ'(G) = Δ(G)` which
need not hold.

## Proof plan

1. `Δ(G □ H) = Δ(G) + Δ(H)` — the `boxProd` degree computation, shared with (a).
2. `≥` from `maxDegree_le_edgeChromaticNumber`.
3. `≤`: from `hH`, split `E(H)` into `Δ(H)` matchings.  For each, the
   corresponding "layer" of `G □ H` is a copy of the part (a) construction; colour
   layer `i` using a palette shifted by `i`.
4. Verify the palettes can be arranged not to clash — the same bookkeeping as
   part (a), now iterated.

⚠ Step 3 again needs the colouring↔matching-partition bridge that the rest of the
chapter wants and that this file never states.  That bridge is required by
Theorem 6.3, exercise 6.1.2, exercise 6.2.3(a) and both halves of 6.2.6 — it is
the most-wanted missing lemma in the file.

## Status

`sorry`, blocked via part (a) on Vizing.
-/
theorem edgeChromaticNumber_boxProd
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    [DecidableRel (G □ H).Adj]
    (hnontriv : 0 < H.maxDegree)
    (hH : H.lineGraph.chromaticNumber = (H.maxDegree : ℕ∞)) :
    (G □ H).lineGraph.chromaticNumber = ((G □ H).maxDegree : ℕ∞) := by
  sorry

-- DROPPED (per outline): Ex 6.1.3(b) (alternative proof of Thm 6.1, not a new statement);
-- Ex 6.1.4 & Ex 6.2.7 (procedural "describe a good algorithm"); Ex 6.3.1 (multigraph computation);
-- general Vizing `Δ ≤ χ′ ≤ Δ+μ` (multiplicity `μ` not representable in `SimpleGraph`; a prose remark).
-- DROPPED (annotation pass): Ex 6.1.5 and Ex 6.2.4(b) — both were stated, but under
-- `SimpleGraph` each collapses to a one-line corollary of Vizing and no longer expresses
-- the exercise.  Book text and the reason are recorded below.

end SimpleGraph
