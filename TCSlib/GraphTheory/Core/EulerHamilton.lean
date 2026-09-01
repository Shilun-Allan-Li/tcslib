import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Multiset.Sort

/-!
# Bondy & Murty, *Graph Theory with Applications* — Chapter 4: Euler Tours and Hamilton Cycles

Sorry-skeleton extracted from `papers/bondy-murty-ch4-euler-hamilton.md`.

Every proof body is `sorry`; this file is a scaffold for sorry-driven development
(fill one stub at a time, `lake build` after each).

The outline's `import TCSlib.GraphTheory.*` lines refer to repo files that are not
importable here, so the small amount of connectivity API needed (`IsVertexCut`,
`vertexConnectivity`, for Ex 4.2.1(a)) is defined locally, mirroring
`TCSlib/GraphTheory/Connectivity.lean`.

Per the outline's Scaffolding audit, the following are **DROPPED** and do NOT appear
below (each was built on a `def … := sorry` predicate, making its theorem content-free,
or is a figure/algorithm outside the chapter):
Lemma 4.4.2, Theorem 4.7 (Fleury), Ex 4.1.3 (blocks), Ex 4.4.1 (TSP), Ex 4.2.13, Ex 4.2.14.
Theorems 4.4, 4.4-corollary, 4.5 and Ex 4.2.1(a) are stated in the audit's **restated** forms.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Key Definitions -/

/-- `G` is **eulerian**: it has a closed Euler trail (an Euler tour).
`[DecidableEq V]` is genuinely required (`Walk.IsEulerian` uses `List.count`).

## Book definition (§4.1, p. 59) — verbatim

> A trail that traverses every edge of $G$ is called an *Euler trail* of $G$
> because Euler was the first to investigate the existence of such trails in
> graphs.

> A *tour* of $G$ is a closed walk that traverses each edge of $G$ at least once.
> An *Euler tour* is a tour which traverses each edge exactly once (in other
> words, a closed Euler trail). A graph is *eulerian* if it contains an Euler
> tour.

## In Lean notation

`∃ u, ∃ p : G.Walk u u, p.IsEulerian` — a closed walk using every edge exactly
once.  Mathlib's `Walk.IsEulerian` is defined via `List.count` on `p.edges`,
which is why `[DecidableEq V]` is genuinely required here and not merely
convenient.

Note the book's three-way vocabulary collapses in Lean: `IsEulerian` already
implies `IsTrail`, so "closed Euler trail" and "Euler tour" are the same
predicate on a `Walk u u`.

## Book motivation (§4.1, p. 59) — verbatim

> In the earliest known paper on graph theory (Euler, 1736), he showed that it
> was impossible to cross each of the seven bridges of Königsberg once and only
> once during a walk through the town. [...] proving that such a walk is
> impossible amounts to showing that the graph of figure 4.1$b$ contains no
> Euler trail.
-/
def IsEulerianGraph {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ (u : V) (p : G.Walk u u), p.IsEulerian

/-- Component count `ω(G)`. Mathlib's own idiom (`Tutte.lean`) is `Nat.card`;
this is a thin shorthand, deliberately **not** named `omega`.

## Book definition (§1.6)

`ω(G)` is the number of components of `G` — the classes into which the
equivalence relation "is connected to" partitions the vertex set.  Defined in
chapter 1, not chapter 4, so there is no chapter-4 text to quote.

## In Lean notation

`Nat.card G.ConnectedComponent`, following Mathlib's own idiom in `Tutte.lean`.
Deliberately **not** named `omega`, which is a tactic.

## Where it is used

Theorem 4.2 only, as the left-hand side of the toughness condition
`ω(G - S) ≤ |S|`: a hamiltonian graph cannot fall into many pieces when few
vertices are deleted.
-/
noncomputable def numComponents {V : Type*} (G : SimpleGraph V) : ℕ := Nat.card G.ConnectedComponent

/-- **Join** `G ∨ H`, rebuilt on Mathlib: within-side edges from `⊕g`, all cross
edges from `completeBipartiteGraph`. `symm`/`loopless` are inherited from `⊔`.

## Book definition (§4.2, p. 66) — verbatim

> We first introduce the notion of the join of two graphs. The *join*
> $G \vee H$ of disjoint graphs $G$ and $H$ is the graph obtained from $G + H$ by
> joining each vertex of $G$ to each vertex of $H$; it is represented
> diagrammatically as in figure 4.8.

## In Lean notation

Lay the two graphs side by side keeping all their own edges, then add every
edge running between them.  The book's `G + H` (disjoint union) is Mathlib's
`⊕g`, and "joining each vertex of `G` to each vertex of `H`" is exactly
`completeBipartiteGraph V W`, so

    join G H = (G ⊕g H) ⊔ completeBipartiteGraph V W

on carrier `V ⊕ W`.  Building it as a `⊔` of two existing graphs means `symm`
and `loopless` are inherited and need no proof.

## Where it is used

The building block of the graphs `Cmn` below.
-/
def join {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) :=
  (G ⊕g H) ⊔ completeBipartiteGraph V W

/-- `C_{m,n} = K_m ∨ (K_m^c + K_{n-2m})`, with `+` the Mathlib disjoint sum `⊕g`.

## Book definition (§4.2, p. 66) — verbatim

> Now, for $1 \le m < n/2$, let $C_{m,n}$ denote the graph
> $K_m \vee (K_m^c + K_{n-2m})$, depicted in figure 4.9a; two specific examples,
> $C_{1,5}$ and $C_{2,5}$, are shown in figures 4.9b and 4.9c.

## In Lean notation

Take `m` "hub" vertices forming a complete graph, `m` isolated vertices, and a
complete graph on the remaining `n - 2m`; then join every hub to everything
else.  Carrier `Fin m ⊕ (Fin m ⊕ Fin (n - 2 * m))`, with `K_mᶜ = ⊥` on `Fin m`.

Degrees: the `m` hubs have degree `n - 1`, the `m` isolated vertices have degree
`m`, and the remaining `n - 2m` have degree `n - m - 1`.  That is the degree
sequence Theorem 4.6 majorises against.

⚠ The side condition `1 ≤ m < n/2` is **not** carried in the type.  For `m = 0`
or `2m > n` the definition still elaborates (with `n - 2 * m` truncating to `0`)
but no longer matches the book's figure.  Callers must supply the bound.

## Book remark (§4.2, p. 67) — verbatim

> That $C_{m,n}$ is nonhamiltonian follows immediately from theorem 4.2; for if
> $S$ denotes the set of $m$ vertices of degree $n-1$ in $C_{m,n}$, we have
> $\omega(C_{m,n} - S) = m + 1 > |S|$.

Theorem 4.6 then shows these are the *extreme* nonhamiltonian graphs: every
nonhamiltonian simple graph is degree-majorised by some `C_{m,ν}`.  `C_{1,ν}`
and `C_{2,5}` reappear as the extremal cases of Corollary 4.6.
-/
def Cmn (m n : ℕ) : SimpleGraph (Fin m ⊕ (Fin m ⊕ Fin (n - 2 * m))) :=
  (⊤ : SimpleGraph (Fin m)).join
    ((⊥ : SimpleGraph (Fin m)) ⊕g (⊤ : SimpleGraph (Fin (n - 2 * m))))

/-- The sorted (ascending) **degree sequence** of `G`.
NOTE: degree is written as `Nat.card (neighborSet)` so the definition works for any
graph without threading a `DecidableRel _.Adj` instance; this equals `G.degree` when
`V` is finite.

## Book definition (exercise 1.5.5; used throughout §4.2)

Listing the vertices as `v₁, …, v_ν`, the sequence `(d(v₁), …, d(v_ν))` is a
degree sequence of `G`.  Chapter 4 always takes it in nondecreasing order — as in
the hypothesis of Theorem 4.5 (§4.2, p. 65):

> Let $G$ be a simple graph with degree sequence $(d_1, d_2, \ldots, d_\nu)$,
> where $d_1 \leq d_2 \leq \ldots \leq d_\nu$ and $\nu \geq 3$.

which is why this definition sorts ascending.

## In Lean notation

Simply list how many neighbours each vertex has, smallest first.

Degree is written `Nat.card (G.neighborSet v)` rather than `G.degree v`, so the
definition works for any graph on a `Fintype` without threading a
`DecidableRel G.Adj` instance; the two agree when `V` is finite.

The book indexes from `1` (`d₁ ≤ … ≤ d_ν`); the Lean list is `0`-indexed, so the
book's `d_m` is `degreeSequence.getD (m - 1) 0`.  Statements below that quote
Theorem 4.5 must account for that shift.

## Where it is used

Chvátal's Theorem 4.5 reads hamiltonicity off this list alone; Theorem 4.6 and
Corollary 4.6 compare two such lists via `DegreeMajorised`.
-/
noncomputable def degreeSequence {V : Type*} [Fintype V] (G : SimpleGraph V) : List ℕ :=
  (Finset.univ.val.map fun v => Nat.card (G.neighborSet v)).sort (· ≤ ·)

/-- `G` is **degree-majorised** by `H`: same order, and every sorted-degree entry of `G`
is ≤ the corresponding entry of `H`.

## Book definition (§4.2, p. 66) — verbatim

> A sequence of real numbers $(p_1, p_2, \ldots, p_n)$ is said to be *majorised*
> by another such sequence $(q_1, q_2, \ldots, q_n)$ if $p_i \le q_i$ for
> $1 \le i \le n$. A graph $G$ is *degree-majorised* by a graph $H$ if
> $\nu(G) = \nu(H)$ and the nondecreasing degree sequence of $G$ is majorised by
> that of $H$. For instance, the 5-cycle is degree-majorised by $K_{2,3}$ because
> $(2, 2, 2, 2, 2)$ is majorised by $(2, 2, 2, 3, 3)$.

## In Lean notation

Line up both degree sequences in increasing order and compare entry by entry;
`G` is degree-majorised by `H` when `H` wins or ties at every position.

Quantifying over *all* `i : ℕ` with `getD i 0` rather than over `Fin ν` is
deliberate: past the end of both lists the comparison is `0 ≤ 0`, so the extra
indices are harmless and no bounds proof has to be threaded through.

## Book context (§4.2, p. 66) — verbatim

> The family of degree-maximal nonhamiltonian graphs (those that are
> degree-majorised by no others) admits of a simple description.

Theorem 4.6 gives that description: every nonhamiltonian graph sits below some
`C_{m,ν}`.
-/
def DegreeMajorised {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  Fintype.card V = Fintype.card W ∧
    ∀ i : ℕ, G.degreeSequence.getD i 0 ≤ H.degreeSequence.getD i 0

/-- One **Bondy–Chvátal closure step**: add a nonadjacent pair whose degree sum is ≥ `ν`.
Honest replacement for a `closure` fixpoint (audit judgement 1/2). Degree is written as
`Nat.card (neighborSet)` so the relation is well-typed for arbitrary graphs on `V`.

## Book definition (§4.2, p. 64) — verbatim

> Lemma 4.4.1 motivates the following definition. The *closure* of $G$ is the
> graph obtained from $G$ by recursively joining pairs of nonadjacent vertices
> whose degree sum is at least $\nu$ until no such pair remains. We denote the
> closure of $G$ by $c(G)$.

## In Lean notation

Look for two vertices not yet joined but which between them already have at
least `ν` neighbours; Lemma 4.4.1 says adding the edge changes nothing about
hamiltonicity, so add it.  Repeat until no such pair is left.

`ClosureStep G H` captures a *single* such addition, `H = G ⊔ edge u v`.  The
closure is then reached by `Relation.ReflTransGen ClosureStep`, and "no such pair
remains" is expressed at the use site as `H = ⊤` or as the absence of a further
step, rather than by a fixpoint operator.

## Why a step relation rather than a `closure` function

Defining `c(G)` as a function presupposes Lemma 4.4.2 — that the result is
independent of the order in which edges are added — and that lemma is itself one
of the chapter's results.  Positing the fixpoint would therefore assume what the
chapter sets out to prove.  Using the step relation keeps the development honest;
the price is that statements below quantify over `ReflTransGen ClosureStep`
chains instead of mentioning `c(G)` directly.

Degree is `Nat.card (G.neighborSet ·)` so the relation is well-typed for
arbitrary graphs on `V` without a `DecidableRel` instance.

## Book statement of the well-definedness result (§4.2, p. 64) — verbatim

> *Lemma 4.4.2* $c(G)$ is well defined.

Its proof (the "first edge not in `G₂`" argument) is quoted on
`hamiltonian_iff_of_closureSteps` below, which is where the content is used.
-/
def ClosureStep (G H : SimpleGraph V) : Prop :=
  ∃ u v : V, ¬ G.Adj u v ∧ u ≠ v ∧
    Fintype.card V ≤ Nat.card (G.neighborSet u) + Nat.card (G.neighborSet v) ∧
    H = G ⊔ SimpleGraph.edge u v

/-- `G` is **Hamilton-connected**: every ordered pair is joined by a Hamilton path (Ex 4.2.11).

## Book definition (exercise 4.2.11, p. 69) — verbatim

> **4.2.11** $G$ is *Hamilton-connected* if every two vertices of $G$ are
> connected by a Hamilton path.
>
> (a) Show that if $G$ is Hamilton-connected and $\nu \ge 4$, then
> $\varepsilon \ge [\frac{1}{2}(3\nu+1)]$.
>
> (b)\* For $\nu \ge 4$, construct a Hamilton-connected graph $G$ with
> $\varepsilon = [\frac{1}{2}(3\nu+1)]$. (J. W. Moon)

## In Lean notation

Not merely that *some* spanning path exists, but that both endpoints may be
prescribed arbitrarily: `∀ u v, u ≠ v → ∃ p : G.Walk u v, p.IsHamiltonian`.

Substantially stronger than being hamiltonian, and correspondingly forces many
edges — part (a) is `hamiltonConnected_edge_bound` below, part (b) is
`exists_extremal_hamiltonConnected`.

The book's `[x]` here denotes the ceiling, so `[½(3ν+1)]` is `(3 * ν + 1 + 1) / 2`
in natural-number division.
-/
def IsHamiltonConnected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → ∃ p : G.Walk u v, p.IsHamiltonian

open scoped Classical in
/-- `G` is **hypohamiltonian**: not Hamiltonian, but every vertex-deleted subgraph is
(Ex 4.2.12). Classical instances discharge the `Fintype`/`DecidableEq` obligations on the
induced-subgraph carrier.

## Book definition (exercise 4.2.12, p. 69) — verbatim

> **4.2.12** $G$ is *hypohamiltonian* if $G$ is not hamiltonian but $G - v$ is
> hamiltonian for every $v \in V$. Show that the Petersen graph (figure 4.4) is
> hypohamiltonian.
>
> (Herz, Duby and Vigué, 1967 have shown that it is, in fact, the smallest such
> graph.)

## In Lean notation

The graph just barely fails to be hamiltonian: no spanning cycle itself, yet
deleting any single vertex repairs the defect.

`G - v` is `G.induce ({v}ᶜ : Set V)`, whose carrier is a *subtype*, so each
`IsHamiltonian` obligation is about a different vertex type.  The `open scoped
Classical in` above the definition is what discharges the resulting
`Fintype`/`DecidableEq` instances on those carriers.

## Where it is used

`petersen_isHypohamiltonian` below — the exercise itself.
-/
def IsHypohamiltonian {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ¬ G.IsHamiltonian ∧ ∀ v : V, (G.induce ({v}ᶜ : Set V)).IsHamiltonian

/-! ### Local connectivity API (mirrors `Connectivity.lean`; for Ex 4.2.1(a)) -/

/-- A **vertex cut**: a proper subset whose deletion leaves `G` disconnected.

## Book definition (§3.1, p. 50) — verbatim

> A *vertex cut* of $G$ is a subset $V'$ of $V$ such that $G - V'$ is
> disconnected. A *$k$-vertex cut* is a vertex cut of $k$ elements.

## In Lean notation

Identical to `SimpleGraph.IsVertexCut` in `Connectivity.lean`; see there for the
discussion of the `↑S ⊂ Set.univ` conjunct.

⚠ Duplicated rather than imported — this file does not depend on
`Connectivity.lean`.  The two definitions are textually identical, so if one is
changed the other must be too.

## Where it is used

Exercise 4.2.1(a) only (`nonhamiltonian_of_not_two_connected`): a graph that is
not 2-connected cannot be hamiltonian.
-/
def IsVertexCut (G : SimpleGraph V) (S : Finset V) : Prop :=
  (↑S : Set V) ⊂ Set.univ ∧ ¬ (G.induce ((↑S : Set V)ᶜ)).Connected

open scoped Classical in
/-- Vertex connectivity `κ(G)`.

## Book definition (§3.1, p. 50) — verbatim

> If $G$ has at least one pair of distinct nonadjacent vertices, the
> *connectivity* $\kappa(G)$ of $G$ is the minimum $k$ for which $G$ has a
> $k$-vertex cut; otherwise, we define $\kappa(G)$ to be $\nu - 1$. [...] $G$ is
> said to be *$k$-connected* if $\kappa(G) \geq k$.

## In Lean notation

Identical to `SimpleGraph.vertexConnectivity` in `Connectivity.lean`; see there
for why the `if` splits on "a vertex cut exists" rather than on the book's "some
pair is nonadjacent".

⚠ Duplicated rather than imported, as with `IsVertexCut` above.

## Where it is used

Exercise 4.2.1(a) only (`nonhamiltonian_of_not_two_connected`).
-/
noncomputable def vertexConnectivity (G : SimpleGraph V) : ℕ :=
  if ∃ S : Finset V, G.IsVertexCut S then
    sInf {n : ℕ | ∃ S : Finset V, G.IsVertexCut S ∧ S.card = n}
  else
    Fintype.card V - 1

/-! ## Theorem 4.1: Euler tour existence (Euler, 1736) -/

/-- Thm 4.1: a nonempty connected graph is eulerian iff it has no odd-degree vertex.

## Book statement (§4.1, p. 59) — verbatim

> *Theorem 4.1*   A nonempty connected graph is eulerian if and only if it has no
> vertices of odd degree.

## Book proof (§4.1, pp. 59–60) — verbatim

> Let $G$ be eulerian, and let $C$ be an Euler tour of $G$ with origin (and
> terminus) $u$. Each time a vertex $v$ occurs as an internal vertex of $C$, two
> of the edges incident with $v$ are accounted for. Since an Euler tour contains
> every edge of $G$, $d(v)$ is even for all $v \neq u$. Similarly, since $C$
> starts and ends at $u$, $d(u)$ is also even. Thus $G$ has no vertices of odd
> degree.
>
> Conversely, suppose that $G$ is a noneulerian connected graph with at least one
> edge and no vertices of odd degree. Choose such a graph $G$ with as few edges as
> possible. Since each vertex of $G$ has degree at least two, $G$ contains a
> closed trail (exercise 1.7.2). Let $C$ be a closed trail of maximum possible
> length in $G$. By assumption, $C$ is not an Euler tour of $G$ and so $G - E(C)$
> has some component $G'$ with $\varepsilon(G') > 0$. Since $C$ is itself
> eulerian, it has no vertices of odd degree; thus the connected graph $G'$ also
> has no vertices of odd degree. Since $\varepsilon(G') < \varepsilon(G)$, it
> follows from the choice of $G$ that $G'$ has an Euler tour $C'$. Now, because
> $G$ is connected, there is a vertex $v$ in $V(C) \cap V(C')$, and we may assume,
> without loss of generality, that $v$ is the origin and terminus of both $C$ and
> $C'$. But then $CC'$ is a closed trail of $G$ with
> $\varepsilon(CC') > \varepsilon(C)$, contradicting the choice of $C$.

## In Lean notation

Every visit to a vertex consumes one edge coming in and one going out, so the
edges at each vertex must pair up.

The (⇐) direction is a *minimal counterexample* argument.  In Lean that is
strong induction on `ε(G)` — the book's "choose such a graph with as few edges
as possible" — generalised over the graph, since `G'` is a different graph on
(the subtype of) the same vertex type.

## Proof plan

(⇒) Given `p : G.Walk u u` with `p.IsEulerian`, use Mathlib's
`Walk.IsEulerian.even_degree_iff`, which already states exactly this: for an
Eulerian trail `p : G.Walk u v`, `Even (G.degree x) ↔ (u = v ∨ x ≠ u ∧ x ≠ v)`.
With `u = v` the right side is trivially true, giving `Even (G.degree x)` for all
`x`.  This direction should be nearly immediate.

(⇐) Strong induction on `G.edgeFinset.card`, generalising `G`:
1. Every degree is even and positive (connected, nonempty edge set), so `≥ 2`;
   extract a closed trail — Mathlib has no direct `exists_closed_trail`, so this
   needs the exercise-1.7.2 argument (walk until a vertex repeats).
2. Take `C` a maximum-length closed trail.  If `C.edges` is all of
   `G.edgeFinset`, done.
3. Otherwise `G.deleteEdges C.edges` has a component `G'` with an edge; degrees
   in `G'` stay even because a closed trail uses an even number of edges at each
   vertex.  Apply the induction hypothesis to `G'`.
4. Splice: `C` and `C'` share a vertex by connectivity; rotate both to that
   vertex (`Walk.rotate`) and append.  The result is a longer closed trail,
   contradicting maximality.

## Status

`sorry`.  (⇒) is the tractable half via `IsEulerian.even_degree_iff`; (⇐) needs
the whole minimal-counterexample apparatus, including a closed-trail
extraction lemma that Mathlib does not provide.
-/
theorem euler_tour_iff_no_odd_degree
    (hne : G.edgeSet.Nonempty) (hconn : G.Connected) :
    G.IsEulerianGraph ↔ ∀ v, Even (G.degree v) := by
  sorry

/-! ## Corollary 4.1: Euler trail existence -/

/-- Cor 4.1: a connected graph has an Euler trail iff at most two vertices have odd degree.

## Book statement (§4.1, p. 60) — verbatim

> *Corollary 4.1* A connected graph has an Euler trail if and only if it has at
> most two vertices of odd degree.

## Book proof (§4.1, p. 60) — verbatim

> If $G$ has an Euler trail then, as in the proof of theorem 4.1, each vertex
> other than the origin and terminus of this trail has even degree.
>
> Conversely, suppose that $G$ is a nontrivial connected graph with at most two
> vertices of odd degree. If $G$ has no such vertices then, by theorem 4.1, $G$
> has a closed Euler trail. Otherwise, $G$ has exactly two vertices, $u$ and $v$,
> of odd degree. In this case, let $G + e$ denote the graph obtained from $G$ by
> the addition of a new edge $e$ joining $u$ and $v$. Clearly, each vertex of
> $G + e$ has even degree and so, by theorem 4.1, $G + e$ has an Euler tour
> $C = v_0 e_1 v_1 \ldots e_{\varepsilon+1} v_{\varepsilon+1}$, where $e_1 = e$.
> The trail $v_1 e_2 v_2 \ldots e_{\varepsilon+1} v_{\varepsilon+1}$ is an Euler
> trail of $G$.

## In Lean notation

By Corollary 1.1 the number of odd-degree vertices is always even, so "at most
two" means exactly `0` or `2`.

This is the precise answer to the Königsberg question and to exercise 4.1.1: a
figure can be drawn "without lifting the pen and without retracing" exactly when
it is connected and has at most two odd-degree vertices.

## Proof plan

(⇒) **Already available in Mathlib.**  `Walk.IsEulerian.card_filter_odd_degree`
states `s.card = 0 ∨ s.card = 2` for `s = univ.filter (Odd (G.degree ·))` —
literally this direction.  Destructure the hypothesis and finish with `omega`.

(⇐) The book's edge-addition trick:
1. Split on whether the odd-degree count is `0` or `2`
   (`even_card_odd_degree` rules out `1`).
2. Count `0`: Theorem 4.1 gives a closed Euler tour, which is an Euler trail
   with `u = v`.
3. Count `2`: let `{u, v}` be the two odd vertices.  ⚠ `u` and `v` may already be
   adjacent, in which case `G ⊔ edge u v = G` and no parity changes — the book's
   "add a new edge" silently assumes a multigraph.  In `SimpleGraph` this case
   must be handled separately (subdivide the existing `uv`, or argue directly),
   which is the one real gap between the book's proof and a Lean one.
4. Otherwise `G ⊔ edge u v` has all degrees even; Theorem 4.1 gives a tour;
   rotate it so the added edge is first (`Walk.rotate`), then drop the first
   step to get an Euler trail of `G`.

## Status

`sorry`.  (⇒) should be a two-liner off Mathlib; (⇐) rests on Theorem 4.1 and on
resolving the already-adjacent case in step 3.
-/
theorem euler_trail_iff_le_two_odd (hconn : G.Connected) :
    (∃ (u v : V) (p : G.Walk u v), p.IsEulerian) ↔
      (Finset.univ.filter fun v => Odd (G.degree v)).card ≤ 2 := by
  sorry

/-! ## Theorem 4.2: necessary condition `ω(G − S) ≤ |S|` -/

/-- Thm 4.2: if `G` is hamiltonian then `ω(G − S) ≤ |S|` for every nonempty proper `S`.

## Book statement (§4.2, p. 61) — verbatim

> **Theorem 4.2** If $G$ is hamiltonian then, for every nonempty proper subset
> $S$ of $V$
> $$\omega(G - S) \le |S| \tag{4.1}$$

## Book proof (§4.2, p. 62) — verbatim

> Let $C$ be a Hamilton cycle of $G$. Then, for every nonempty proper subset $S$
> of $V$
> $$\omega(C - S) \le |S|$$
> Also, $C - S$ is a spanning subgraph of $G - S$ and so
> $$\omega(G - S) \le \omega(C - S)$$
> The theorem follows.

## In Lean notation

A hamiltonian graph is held together by a single cycle through every vertex, and
a cycle is hard to shatter: removing `k` vertices from it leaves at most `k`
arcs.

`G - S` is rendered as `((⊤ : G.Subgraph).deleteVerts ↑S).coe`, so the component
count is `Nat.card` of *that* graph's `ConnectedComponent`.  Using the `Subgraph`
API rather than `G.induce (↑S)ᶜ` is what lets the "spanning subgraph" step be
stated at all, since `C - S` and `G - S` then live over the same vertex set.

## Proof plan

1. Obtain a Hamilton cycle `C` from `hG`.
2. `ω(C - S) ≤ |S|`: the book's "clearly".  In Lean this is the real work —
   induct along the cycle, or map each component of `C - S` injectively to the
   vertex of `S` that terminates its arc.
3. `ω(G - S) ≤ ω(C - S)`: components can only merge when edges are added, so the
   component-count map induced by the subgraph inclusion is surjective.
4. Chain.

## Book remarks (§4.2, p. 62) — verbatim

> As an illustration of the above theorem, consider the graph of figure 4.3. This
> graph has nine vertices; on deleting the three indicated in black, four
> components remain. Therefore (4.1) is not satisfied and it follows from theorem
> 4.2 that the graph is nonhamiltonian.

> We thus see that theorem 4.2 can sometimes be applied to show that a particular
> graph is nonhamiltonian. However, this method does not always work; for
> instance, the Petersen graph (figure 4.4) is nonhamiltonian, but one cannot
> deduce this by using theorem 4.2.

## Status

`sorry`.  Step 2 is the substantial one.
-/
theorem hamiltonian_toughness (hG : G.IsHamiltonian) (S : Finset V)
    (hS : S.Nonempty) (hSne : S ≠ Finset.univ) :
    Nat.card ((⊤ : G.Subgraph).deleteVerts ↑S).coe.ConnectedComponent ≤ S.card := by
  sorry

/-! ## Theorem 4.3: Dirac's condition (Dirac, 1952) -/

/-- Thm 4.3: `ν ≥ 3` and `δ ≥ ν/2` (stated as `ν ≤ 2δ`) imply `G` is hamiltonian.

## Book statement (§4.2, p. 62) — verbatim

> *Theorem 4.3* If $G$ is a simple graph with $\nu \ge 3$ and
> $\delta \ge \nu/2$, then $G$ is hamiltonian.

## Book proof (§4.2, pp. 62–63) — verbatim

> By contradiction. Suppose that the theorem is false, and let $G$ be a maximal
> nonhamiltonian simple graph with $\nu \ge 3$ and $\delta \ge \nu/2$. Since
> $\nu \ge 3$, $G$ cannot be complete. Let $u$ and $v$ be nonadjacent vertices in
> $G$. By the choice of $G$, $G + uv$ is hamiltonian. Moreover, since $G$ is
> nonhamiltonian, each Hamilton cycle of $G + uv$ must contain the edge $uv$.
> Thus there is a Hamilton path $v_1 v_2 \ldots v_\nu$ in $G$ with origin
> $u = v_1$ and terminus $v = v_\nu$. Set
> $$S = \{v_i \mid uv_{i+1} \in E\} \quad \text{and} \quad T = \{v_i \mid v_i v \in E\}$$
> Since $v_\nu \notin S \cup T$ we have
> $$|S \cup T| < \nu \tag{4.2}$$
> Furthermore
> $$|S \cap T| = 0 \tag{4.3}$$
> since if $S \cap T$ contained some vertex $v_i$, then $G$ would have the
> Hamilton cycle $v_1 v_2 \ldots v_i v_\nu v_{\nu-1} \ldots v_{i+1} v_1$, contrary
> to assumption (see figure 4.5).
>
> Using (4.2) and (4.3) we obtain
> $$d(u) + d(v) = |S| + |T| = |S \cup T| + |S \cap T| < \nu \tag{4.4}$$
> But this contradicts the hypothesis that $\delta \geq \nu/2$.

## In Lean notation

If every vertex is joined to at least half the graph, there is enough adjacency
that a spanning cycle cannot be avoided.

`δ ≥ ν/2` is formalised as `ν ≤ 2δ` to stay in the natural numbers and avoid the
rounding ambiguity of `ν/2` under truncated division.

## Proof plan

The book's "let `G` be a maximal nonhamiltonian graph" is an extremal-choice
argument over the finite lattice `SimpleGraph V`.  Two options in Lean:

* **Direct** — mirror the book: `Set.Finite.exists_maximal_wrt` on
  `{H | G ≤ H ∧ ¬ H.IsHamiltonian}`, then run the `S`/`T` counting argument.
* **Via the closure** (recommended) — the book itself notes after Corollary 4.4
  that *"since $c(G)$ is clearly complete when $\delta \geq \nu/2$, Dirac's
  condition (theorem 4.3) is an immediate corollary."*  So: show `δ ≥ ν/2`
  forces `ReflTransGen ClosureStep G ⊤` (any two nonadjacent vertices have
  degree sum `≥ 2δ ≥ ν`), then apply `hamiltonian_of_closureSteps_top`.

The second route avoids re-proving the `S`/`T` count, which is already the
content of `bondy_chvatal` below.

## Status

`sorry`.  Note the file orders Dirac *before* the closure machinery, so taking
the recommended route means this proof forward-references
`hamiltonian_of_closureSteps_top`; either reorder, or accept the direct route.
-/
theorem dirac_hamiltonian (hν : 3 ≤ Fintype.card V)
    (hδ : Fintype.card V ≤ 2 * G.minDegree) :
    G.IsHamiltonian := by
  sorry

/-! ## Lemma 4.4.1: Bondy–Chvátal lemma (1974) -/

/-- Lem 4.4.1: for nonadjacent `u,v` with `d(u)+d(v) ≥ ν`, `G` is hamiltonian iff `G+uv` is.

## Book statement (§4.2, pp. 63–64) — verbatim

> **Lemma 4.4.1** Let $G$ be a simple graph and let $u$ and $v$ be nonadjacent
> vertices in $G$ such that
> $$d(u) + d(v) \geq \nu \tag{4.5}$$
> Then $G$ is hamiltonian if and only if $G + uv$ is hamiltonian.

## Book proof (§4.2, p. 64) — verbatim

> If $G$ is hamiltonian then, trivially, so too is $G + uv$. Conversely, suppose
> that $G + uv$ is hamiltonian but $G$ is not. Then, as in the proof of theorem
> 4.3, we obtain (4.4). But this contradicts hypothesis (4.5).

## In Lean notation

The book's proof is two sentences only because it *reuses* the `S`/`T` counting
argument (4.4) from Theorem 4.3.  In Lean that argument has to exist somewhere
concrete — so this lemma, not Dirac, is the right place to write it out, and
Dirac then follows from the closure machinery.

Expanded, (4.4) is: from a Hamilton cycle of `G + uv` that must use `uv`, extract
a Hamilton path `v₁ … v_ν` in `G` with `v₁ = u`, `v_ν = v`.  Put
`S = {vᵢ | u ~ v_{i+1}}` and `T = {vᵢ | vᵢ ~ v}`.  Then `v_ν ∉ S ∪ T` gives
`|S ∪ T| < ν`, and `S ∩ T = ∅` because a common `vᵢ` would close the Hamilton
cycle `v₁ … vᵢ v_ν v_{ν-1} … v_{i+1} v₁` in `G`.  Hence
`d(u) + d(v) = |S| + |T| < ν`.

## Proof plan

(→) `IsHamiltonian` is monotone in the graph: a cycle of `G` is a cycle of
`G ⊔ edge u v` under `Walk.mapLe le_sup_left`.

(←) By contradiction, as above:
1. Take a Hamilton cycle `c` of `G ⊔ edge u v`.  If `s(u,v) ∉ c.edges` then `c`
   already lives in `G` (`Walk.transfer`), contradicting `¬ G.IsHamiltonian`.
2. Otherwise rotate `c` so `uv` is the first edge and drop it, yielding a
   Hamilton path `p : G.Walk u v`.
3. Define `S`, `T` as `Finset`s indexed along `p.support`.
4. `v ∉ S ∪ T` (no loops), so `|S ∪ T| < ν`.
5. `Disjoint S T`, else splice the reversal to build a Hamilton cycle of `G`.
   This splice is the fiddliest step: it needs `p.takeUntil`/`p.dropUntil` and a
   `reverse` on the second segment.
6. `|S| = d(u)` and `|T| = d(v)` by the indexing bijections, so
   `d(u) + d(v) = |S ∪ T| + |S ∩ T| < ν`, contradicting `hdeg`.

## Book significance (§4.2, p. 63) — verbatim

> Bondy and Chvátal (1974) observed that the proof of theorem 4.3 can be modified
> to yield stronger sufficient conditions than that obtained by Dirac. The basis
> of their approach is the following lemma.

Edges whose endpoints have large combined degree are irrelevant to
hamiltonicity and may be freely added; iterating this produces the closure.

## Status

`sorry`.  This is the load-bearing lemma of §4.2 — Theorem 4.4, Corollary 4.4,
Dirac and Chvátal all reduce to it.
-/
theorem bondy_chvatal {u v : V} (huv : ¬ G.Adj u v) (hne : u ≠ v)
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian ↔ (G ⊔ SimpleGraph.edge u v).IsHamiltonian := by
  sorry

/-! ## Theorem 4.4: hamiltonian ⇔ closure hamiltonian (restated over `ClosureStep`) -/

/-- Thm 4.4 (honest restatement): reachability by closure steps preserves hamiltonicity.

## Book statement (§4.2, p. 65) — verbatim

> **Theorem 4.4** A simple graph is hamiltonian if and only if its closure is
> hamiltonian.

## Book proof (§4.2, p. 65) — verbatim

> Apply lemma 4.4.1 each time an edge is added in the formation of the closure.

## In Lean notation

Stated in the file's "honest restatement" form: instead of positing a closure
operator, it says that if `H` is reachable from `G` by any finite chain of
`ClosureStep`s, then `G` is hamiltonian exactly when `H` is.  Taking `H` to admit
no further step recovers the book's statement.

This restatement is what lets the file skip Lemma 4.4.2 entirely — see below.

## Proof plan

`Relation.ReflTransGen.head_induction_on` (or `.trans_induction_on`) over the
chain:
* refl case — `Iff.rfl`;
* step case — the step gives `u, v` nonadjacent with `ν ≤ d(u) + d(v)` and
  `H = G ⊔ edge u v`, which is exactly `bondy_chvatal`'s hypothesis; compose
  with the inductive `Iff`.

One wrinkle: `ClosureStep` measures degree with `Nat.card (neighborSet ·)` while
`bondy_chvatal` takes `G.degree`.  These agree on a `Fintype` but not
syntactically, so a bridging rewrite (`Nat.card_eq_fintype_card` plus
`card_neighborSet_eq_degree`) is needed at the junction.

## Note on Lemma 4.4.2 (well-definedness of `c(G)`)

The book must prove `c(G)` well defined before Theorem 4.4 can even be stated;
its proof (§4.2, p. 64) is the argument:

> If possible, let $e_{k+1} = uv$ be the first edge in the sequence
> $e_1, e_2, \ldots, e_n$ that is not an edge of $G_2$. [...] This is a
> contradiction, since $u$ and $v$ are nonadjacent in $G_2$. Therefore each $e_i$
> is an edge of $G_2$ and, similarly, each $f_j$ is an edge of $G_1$. Hence
> $G_1 = G_2$, and $c(G)$ is well defined.

Because this file quantifies over `ReflTransGen ClosureStep` chains rather than
naming a closure, **Lemma 4.4.2 is not needed and is not formalised**: the
statement above holds for *every* chain, confluent or not.  It would only be
required if a `closure : SimpleGraph V → SimpleGraph V` function were introduced.

## Status

`sorry`, but this should be short once `bondy_chvatal` lands — it is pure
induction over the chain.
-/
theorem hamiltonian_iff_of_closureSteps {G H : SimpleGraph V}
    (h : Relation.ReflTransGen ClosureStep G H) :
    G.IsHamiltonian ↔ H.IsHamiltonian := by
  sorry

/-! ## Corollary 4.4: complete closure ⇒ hamiltonian (restated) -/

/-- Cor 4.4 (honest restatement): if closure steps reach `⊤`, then `G` was hamiltonian.

## Book statement (§4.2, p. 65) — verbatim

> **Corollary 4.4** Let $G$ be a simple graph with $\nu \geq 3$. If $c(G)$ is
> complete, then $G$ is hamiltonian.

The book gives no separate proof, deriving it from Theorem 4.4 together with:

> upon making the trivial observation that all complete graphs on at least three
> vertices are hamiltonian, we obtain the following result.

## In Lean notation

Stated with `⊤` in place of "`c(G)` is complete", and `ClosureStep` reachability
in place of the closure operator.

## Proof plan

`(hamiltonian_iff_of_closureSteps h).mpr (top_isHamiltonian hν)` — a one-liner
once both inputs exist.

## Book remarks (§4.2, p. 65) — verbatim

> Consider, for example, the graph of figure 4.7. One readily checks that its
> closure is complete. Therefore, by corollary 4.4, it is hamiltonian. It is
> perhaps interesting to note that the graph of figure 4.7 can be obtained from
> the graph of figure 4.3 by altering just one end of one edge, and yet we have
> results (corollary 4.4 and theorem 4.2) which tell us that this one is
> hamiltonian whereas the other is not.

> since $c(G)$ is clearly complete when $\delta \geq \nu/2$, Dirac's condition
> (theorem 4.3) is an immediate corollary.

That last sentence is the recommended route to `dirac_hamiltonian` above.

## Status

`sorry`, pending `hamiltonian_iff_of_closureSteps` and `top_isHamiltonian`.
-/
theorem hamiltonian_of_closureSteps_top (hν : 3 ≤ Fintype.card V)
    (h : Relation.ReflTransGen ClosureStep G ⊤) :
    G.IsHamiltonian := by
  sorry

/-- Reusable helper (⚠ absent from Mathlib): `⊤` on ≥ 3 vertices is hamiltonian.

## Book remark (§4.2, p. 65) — verbatim

> upon making the trivial observation that all complete graphs on at least three
> vertices are hamiltonian

## In Lean notation

In `Kₙ` every pair of distinct vertices is adjacent, so any enumeration
`v₁ v₂ … v_n v₁` is already a Hamilton cycle.  Three vertices are needed because
a cycle must have length at least three — `K₁` and `K₂` have no cycle at all.

⚠ Despite the book calling it "trivial", **Mathlib has no such lemma**, and it is
not trivial in Lean: it requires exhibiting a concrete cyclic enumeration of `V`
and proving the resulting walk is a cycle whose support is nodup and spans.

## Proof plan

1. Pick `e : V ≃ Fin n` from `Fintype.equivFin`, `n = ν ≥ 3`.
2. Build the walk visiting `e.symm 0, e.symm 1, …, e.symm (n-1), e.symm 0` by
   induction on `n`; every consecutive pair is distinct hence `⊤`-adjacent.
3. `IsHamiltonianCycle` needs `IsCycle` (support nodup apart from endpoints,
   length ≥ 3) plus every vertex visited — both follow from `e.symm` being a
   bijection and the index list being `List.range n`.

## Status

`sorry`.  Reusable well beyond this chapter, so worth doing properly.
-/
theorem top_isHamiltonian (hν : 3 ≤ Fintype.card V) :
    (⊤ : SimpleGraph V).IsHamiltonian := by
  sorry

/-! ## Theorem 4.5: Chvátal's condition (Chvátal, 1972) — counting restatement -/

/-- Thm 4.5 (counting form): the Chvátal degree condition implies hamiltonicity.

## Book statement (§4.2, p. 65) — verbatim

> **Theorem 4.5** Let $G$ be a simple graph with degree sequence
> $(d_1, d_2, \ldots, d_\nu)$, where $d_1 \leq d_2 \leq \ldots \leq d_\nu$ and
> $\nu \geq 3$. Suppose that there is no value of $m$ less than $\nu/2$ for which
> $d_m \leq m$ and $d_{\nu-m} < \nu - m$. Then $G$ is hamiltonian.

## Book proof (§4.2, p. 66) — verbatim

> Let $G$ satisfy the hypothesis of the theorem. We shall show that its closure
> $c(G)$ is complete, and the conclusion will then follow from corollary 4.4. We
> denote the degree of a vertex $v$ in $c(G)$ by $d'(v)$.
>
> Assume that $c(G)$ is not complete, and let $u$ and $v$ be two nonadjacent
> vertices in $c(G)$ with
> $$d'(u) \le d'(v) \tag{4.6}$$
> and $d'(u) + d'(v)$ as large as possible; since no two nonadjacent vertices in
> $c(G)$ can have degree sum $\nu$ or more, we have
> $$d'(u) + d'(v) < \nu \tag{4.7}$$
> Now denote by $S$ the set of vertices in $V \backslash \{v\}$ which are
> nonadjacent to $v$ in $c(G)$, and by $T$ the set of vertices in
> $V \backslash \{u\}$ which are nonadjacent to $u$ in $c(G)$. Clearly
> $$|S| = \nu - 1 - d'(v) \quad \text{and} \quad |T| = \nu - 1 - d'(u) \tag{4.8}$$
> Furthermore, by the choice of $u$ and $v$, each vertex in $S$ has degree at most
> $d'(u)$ and each vertex in $T \cup \{u\}$ has degree at most $d'(v)$. Setting
> $d'(u) = m$ and using (4.7) and (4.8), we find that $c(G)$ has at least $m$
> vertices of degree at most $m$ and at least $\nu - m$ vertices of degree less
> than $\nu - m$. Because $G$ is a spanning subgraph of $c(G)$, the same is true
> of $G$; therefore $d_m \le m$ and $d_{\nu-m} < \nu - m$. But this is contrary to
> hypothesis since, by (4.6) and (4.7), $m < \nu/2$. We conclude that $c(G)$ is
> indeed complete and hence, by corollary 4.4, that $G$ is hamiltonian.

## In Lean notation

⚠ The hypothesis is formalised in **counting form**, not by indexing the sorted
degree sequence.  The book's `d_m ≤ m` says "at least `m` vertices have degree
`≤ m`", and `d_{ν-m} < ν - m` says "at least `ν - m` vertices have degree
`< ν - m`" — precisely the two `Finset.filter` cardinalities in `hcond`.  This
avoids all `1`- versus `0`-indexing hazards around `degreeSequence`, at the cost
of no longer looking like the book's inequality.

The book's `m < ν/2` is written `2 * m < ν`, and `m ≥ 1` is made explicit
(the book's `m` is a degree `d'(u)`, and `m = 0` is excluded by connectivity
considerations implicit in "as large as possible").

## Proof plan

1. Show the closure is complete, i.e. `ReflTransGen ClosureStep G ⊤`, then apply
   `hamiltonian_of_closureSteps_top`.
2. For step 1, by contradiction: suppose a maximal chain ends at some `H ≠ ⊤`.
   Choose nonadjacent `u, v` in `H` maximising `d_H(u) + d_H(v)`
   (`Finset.exists_max_image` over the nonadjacent pairs).
3. `d_H(u) + d_H(v) < ν`, else a further `ClosureStep` applies.
4. Build `S`, `T` as in the book and derive the two counting facts, transferring
   them from `H` down to `G` by `G ≤ H` and degree monotonicity.
5. Instantiate `hcond` at `m = d_H(u)` for the contradiction.

## Book remark (§4.2, p. 66) — verbatim

> One can often deduce that a given graph is hamiltonian simply by computing its
> degree sequence and applying theorem 4.5. This method works with the graph of
> figure 4.7 but not with the graph $G$ of figure 4.6, even though the closure of
> the latter graph is complete. From these examples, we see that theorem 4.5 is
> stronger than theorem 4.3 but not as strong as corollary 4.4.

## Status

`sorry`.  Step 4 is the bulk of the work.
-/
theorem chvatal_hamiltonian (hν : 3 ≤ Fintype.card V)
    (hcond : ∀ m : ℕ, 1 ≤ m → 2 * m < Fintype.card V →
      ¬ (m ≤ (Finset.univ.filter fun v => G.degree v ≤ m).card ∧
         Fintype.card V - m ≤
           (Finset.univ.filter fun v => G.degree v < Fintype.card V - m).card)) :
    G.IsHamiltonian := by
  sorry

/-! ## Theorem 4.6: Chvátal degree-majorisation (Chvátal, 1972) -/

/-- Thm 4.6: a nonhamiltonian simple graph with `ν ≥ 3` is degree-majorised by some `C_{m,ν}`.

## Book statement (§4.2, p. 67) — verbatim

> **Theorem 4.6** (Chvátal, 1972)  If $G$ is a nonhamiltonian simple graph with
> $\nu \geq 3$, then $G$ is degree-majorised by some $C_{m,\nu}$.

## Book proof (§4.2, p. 67) — verbatim

> Let $G$ be a nonhamiltonian simple graph with degree sequence
> $(d_1, d_2, \ldots, d_\nu)$, where $d_1 \leq d_2 \leq \ldots \leq d_\nu$ and
> $\nu \geq 3$. Then, by theorem 4.5, there exists $m < \nu/2$ such that
> $d_m \leq m$ and $d_{\nu-m} < \nu - m$. Therefore
> $(d_1, d_2, \ldots, d_\nu)$ is majorised by the sequence
> $$(m, \ldots, m, \nu - m - 1, \ldots, \nu - m - 1, \nu - 1, \ldots, \nu - 1)$$
> with $m$ terms equal to $m$, $\nu - 2m$ terms equal to $\nu - m - 1$ and $m$
> terms equal to $\nu - 1$, and this latter sequence is the degree sequence of
> $C_{m,\nu}$.

## In Lean notation

The family `{C_{m,ν}}` consists of the **degree-maximal** nonhamiltonian graphs:
any nonhamiltonian graph has degrees dominated, position by position, by one of
them.

## Proof plan

1. Contrapose `chvatal_hamiltonian` to obtain `m` with `1 ≤ m`, `2m < ν`, and the
   two counting facts.
2. Convert the counting facts back into sorted-sequence form: "at least `m`
   vertices of degree `≤ m`" gives `degreeSequence.getD (m-1) 0 ≤ m`, and
   similarly for the other.  ⚠ This is the inverse of the translation made in
   `chvatal_hamiltonian`, and is where the `1`-vs-`0` indexing shift noted on
   `degreeSequence` must be handled carefully.
3. Compute `(Cmn m ν).degreeSequence` explicitly as the three-block list above.
4. Compare entrywise: below index `m` use fact one, in the middle block use
   monotonicity of the sorted sequence plus fact two, and in the top block use
   the trivial bound `d ≤ ν - 1`.

## Where it leads

Corollary 4.6 — bounding the edge count of a nonhamiltonian graph reduces to
computing `ε(C_{m,ν})`.

## Status

`sorry`.  Step 3 requires a degree computation for `Cmn` that does not exist in
the file yet.
-/
theorem chvatal_degree_majorised (hν : 3 ≤ Fintype.card V) (hnh : ¬ G.IsHamiltonian) :
    ∃ m : ℕ, 0 < m ∧ 2 * m < Fintype.card V ∧
      DegreeMajorised G (Cmn m (Fintype.card V)) := by
  sorry

/-! ## Corollary 4.6: Ore/Bondy edge bound (Ore 1961, Bondy 1972) — split -/

/-- Cor 4.6a: `ε > C(ν−1,2) + 1` implies hamiltonicity.

## Book statement (§4.2, p. 68) — verbatim, first half

> **Corollary 4.6** If $G$ is a simple graph with $\nu \geq 3$ and
> $\varepsilon > \binom{\nu-1}{2} + 1$, then $G$ is hamiltonian.

## Book proof (§4.2, p. 68) — verbatim

> Let $G$ be a nonhamiltonian simple graph with $\nu \geq 3$. By theorem 4.6, $G$
> is degree-majorised by $C_{m,\nu}$ for some positive integer $m < \nu/2$.
> Therefore, by theorem 1.1,
> $$\varepsilon(G) \leq \varepsilon(C_{m,\nu}) \tag{4.9}$$
> $$= \tfrac{1}{2}(m^2 + (\nu - 2m)(\nu - m - 1) + m(\nu - 1))$$
> $$= \binom{\nu-1}{2} + 1 - \tfrac{1}{2}(m-1)(m-2) - (m-1)(\nu - 2m - 1)$$
> $$\leq \binom{\nu-1}{2} + 1 \tag{4.10}$$

## In Lean notation

Enough edges guarantee a spanning cycle, and this pins down exactly how many
"enough" is: a nonhamiltonian graph has at most `C(ν-1, 2) + 1` edges.

"By theorem 1.1" is the handshaking lemma — degree majorisation transfers to an
edge-count inequality because `2ε = ∑ d(v)`.

⚠ The book's algebra is over `ℚ` (note the `½`); in `ℕ` the identity
`½(m² + (ν-2m)(ν-m-1) + m(ν-1)) = C(ν-1,2) + 1 - ½(m-1)(m-2) - (m-1)(ν-2m-1)`
involves subtraction that truncates.  Either clear denominators and work with
`2ε` throughout, or cast to `ℤ`/`ℚ` for the identity and cast back.  The latter
is likely cleaner.

## Proof plan

1. By contradiction: assume `¬ G.IsHamiltonian`.
2. `chvatal_degree_majorised` gives `m` and `DegreeMajorised G (Cmn m ν)`.
3. Sum the majorised degree sequences and apply handshaking on both sides to get
   `ε(G) ≤ ε(Cmn m ν)`.  This needs a lemma "degree-majorised implies
   `edgeFinset.card ≤`", which is not in the file yet.
4. Compute `ε(Cmn m ν)` in closed form and prove
   `2 * ε(Cmn m ν) ≤ 2 * (C(ν-1,2) + 1)` by `nlinarith`/`ring_nf` after casting.
5. Contradict `hε`.

## Status

`sorry`.  Steps 3 and 4 are both missing infrastructure.
-/
theorem ore_bondy_edge_bound (hν : 3 ≤ Fintype.card V)
    (hε : (Fintype.card V - 1).choose 2 + 1 < G.edgeFinset.card) :
    G.IsHamiltonian := by
  sorry

/-- Cor 4.6b: the extremal nonhamiltonian graphs at `C(ν−1,2)+1` edges are `C_{1,ν}` (and `C_{2,5}`).

## Book statement (§4.2, p. 68) — verbatim, second half

> Moreover, the only nonhamiltonian simple graphs with $\nu$ vertices and
> $\binom{\nu-1}{2} + 1$ edges are $C_{1,\nu}$ and, for $\nu = 5$, $C_{2,5}$.

## Book proof (§4.2, p. 68) — verbatim

> Furthermore, equality can only hold in (4.9) if $G$ has the same degree sequence
> as $C_{m,\nu}$; and equality can only hold in (4.10) if either $m = 2$ and
> $\nu = 5$, or $m = 1$. Hence $\varepsilon(G)$ can equal
> $\binom{\nu-1}{2} + 1$ only if $G$ has the same degree sequence as $C_{1,\nu}$
> or $C_{2,5}$, which is easily seen to imply that $G \cong C_{1,\nu}$ or
> $G \cong C_{2,5}$.

## In Lean notation

The equality analysis of the first half.  The final inequality is tight only when
both subtracted terms `½(m-1)(m-2)` and `(m-1)(ν-2m-1)` vanish, which happens
only for `m = 1`, or `m = 2` together with `ν = 5`.

So the bound is attained by exactly one graph for each `ν`, plus one sporadic
extra at `ν = 5`: the densest nonhamiltonian simple graphs there are.

⚠ The book's closing "which is easily seen to imply that $G \cong C_{1,\nu}$" is
the hardest step to formalise, and it is **not** easy in Lean.  Degree sequence
does not in general determine a graph up to isomorphism; the implication holds
here only because of the specific structure of `C_{1,ν}` and `C_{2,5}`, and
recovering an explicit `≃g` requires constructing the vertex bijection by hand.

## Proof plan

1. Re-run the chain of the first half, tracking equality.
2. From `ε(G) = C(ν-1,2) + 1` deduce equality throughout, hence `m = 1`, or
   `m = 2 ∧ ν = 5`.
3. Deduce `G` has the same degree sequence as `C_{1,ν}` (resp. `C_{2,5}`).
4. Build the isomorphism explicitly: for `C_{1,ν}`, identify the unique vertex of
   degree `ν - 1` and the unique vertex of degree `1`, and map the rest by any
   bijection of the complete remainder.  For `C_{2,5}` a finite check suffices
   (`decide` may be viable at `ν = 5`).

## Status

`sorry`.  Step 4 is the real obstacle and has no book counterpart to lean on.
-/
theorem ore_bondy_extremal (hν : 3 ≤ Fintype.card V) (hnh : ¬ G.IsHamiltonian)
    (hε : G.edgeFinset.card = (Fintype.card V - 1).choose 2 + 1) :
    Nonempty (G ≃g Cmn 1 (Fintype.card V)) ∨
      (Fintype.card V = 5 ∧ Nonempty (G ≃g Cmn 2 5)) := by
  sorry

/-! ## Exercises -/

/-- Ex 4.1.4: no odd degree ⇒ an edge-disjoint decomposition into cycles.

## Book statement (§4.1, p. 61) — verbatim

> 4.1.4 Show that if $G$ has no vertices of odd degree, then there are
> edge-disjoint cycles $C_1, C_2, \ldots, C_m$ such that
> $E(G) = E(C_1) \cup E(C_2) \cup \ldots \cup E(C_m)$.

An exercise, so the book gives no proof.

## In Lean notation

Even degrees everywhere means no "loose ends".  Peel cycles off one at a time:
removing a cycle subtracts `2` from the degree of each vertex it visits, so all
degrees stay even and the argument repeats until no edges are left.

"`E(G) = ⋃ E(Cᵢ)` with the `Cᵢ` edge-disjoint" is rendered as the single
`∃!` statement — every edge lies in exactly one of the cycles — which packages
covering and disjointness together.

Note this needs **no connectivity hypothesis**: it is the local content of
Euler's theorem.  Connectivity is what additionally lets the cycles be spliced
into one tour (Theorem 4.1).

## Proof plan

Strong induction on `G.edgeFinset.card`, generalising `G`:
1. No edges ⇒ take `cs = ∅`; the `∃!` is vacuous.
2. Otherwise all degrees are even and some is positive, so `≥ 2`; extract a cycle
   (exercise 1.7.2 — the same missing lemma that Theorem 4.1's (⇐) needs).
3. Delete its edges; degrees drop by `2` at each visited vertex, so all stay
   even, and the edge count strictly decreases.
4. Apply the induction hypothesis and insert the peeled cycle into `cs`.  The
   `∃!` for the new cycle's edges holds because they were deleted in step 3.

## Status

`sorry`.  Shares the cycle-extraction gap with Theorem 4.1; worth proving that
helper once and reusing it here, in Theorem 4.1, and in Ex 4.1.5.
-/
theorem even_degree_cycle_decomposition (h : ∀ v, Even (G.degree v)) :
    ∃ cs : Finset (Σ u : V, G.Walk u u),
      (∀ c ∈ cs, c.2.IsCycle) ∧
      ∀ e ∈ G.edgeSet, ∃! c : (Σ u : V, G.Walk u u), c ∈ cs ∧ e ∈ c.2.edges := by
  sorry

/-- Ex 4.1.5: exactly `2k` odd-degree vertices ⇒ `k` edge-disjoint covering trails.

## Book statement (§4.1, p. 61) — verbatim

> 4.1.5 Show that if a connected graph $G$ has $2k > 0$ vertices of odd degree,
> then there are $k$ edge-disjoint trails $Q_1, Q_2, \ldots, Q_k$ in $G$ such
> that $E(G) = E(Q_1) \cup E(Q_2) \cup \ldots \cup E(Q_k)$.

An exercise, so the book gives no proof.

## In Lean notation

By Corollary 1.1 the odd-degree vertices come in pairs, so there are `k` pairs.
Pair them up and add `k` new edges joining the members of each pair; every vertex
of the enlarged graph then has even degree, so Theorem 4.1 gives an Euler tour.
Deleting the `k` added edges cuts that tour into exactly `k` trails, which are
edge-disjoint and between them cover every edge of `G`.

The practical reading: a road network with `2k` awkward junctions needs `k`
separate pen-strokes; one Euler trail is the case `k = 1`.

## Proof plan

1. Extract the `2k` odd-degree vertices and choose a pairing (any perfect
   matching on that `Finset`; existence is just `Finset.card` even).
2. ⚠ Same obstacle as Corollary 4.1: adding an edge between an already-adjacent
   pair does nothing in a `SimpleGraph`.  Here it is worse, since `k` edges are
   added at once and several pairs may already be adjacent.  Either move to a
   multigraph encoding for the intermediate step, or pick the pairing to avoid
   existing edges — which is not always possible.
3. Apply Theorem 4.1 to the enlarged graph for an Euler tour.
4. Split the tour at the `k` added edges, giving `k` trails; `ts.card = k` and
   the `∃!` covering follow from the tour being Eulerian.

## Status

`sorry`.  Step 2 is a genuine modelling problem, not just labour — it is the
same `SimpleGraph`-versus-multigraph mismatch flagged on `euler_trail_iff_le_two_odd`.
-/
theorem odd_vertices_trail_cover (k : ℕ) (hk : 0 < k) (hconn : G.Connected)
    (h : (Finset.univ.filter fun v => Odd (G.degree v)).card = 2 * k) :
    ∃ ts : Finset (Σ p : V × V, G.Walk p.1 p.2),
      ts.card = k ∧ (∀ t ∈ ts, t.2.IsTrail) ∧
      ∀ e ∈ G.edgeSet, ∃! t : (Σ p : V × V, G.Walk p.1 p.2), t ∈ ts ∧ e ∈ t.2.edges := by
  sorry

/-- Ex 4.2.1(a): not 2-connected (with `ν ≥ 3`) ⇒ nonhamiltonian
(restated on the repo `vertexConnectivity`).

## Book statement (§4.2, p. 68) — verbatim

> 4.2.1 Show that if either
>
> (a) $G$ is not 2-connected, or
> (b) $G$ is bipartite with bipartition $(X, Y)$ where $|X| \neq |Y|$,
> then $G$ is nonhamiltonian.

An exercise, so the book gives no proof.

## In Lean notation

A graph that is not 2-connected is either disconnected or has a cut vertex `v`.
Disconnected: no cycle reaches every vertex.  Cut vertex: take `S = {v}` in
Theorem 4.2 — deleting `v` leaves at least two components, so
`ω(G - S) ≥ 2 > 1 = |S|`, violating the necessary condition.

A Hamilton cycle visits every vertex and returns, which needs two independent
routes out of every vertex — exactly 2-connectivity.  Necessary but far from
sufficient (the Petersen graph is 3-connected and nonhamiltonian).

Stated against this file's local `vertexConnectivity`, not the one in
`Connectivity.lean` — see the warning on that definition above.

## Proof plan

1. `¬ (2 ≤ κ)` means `κ ≤ 1`; unfold `vertexConnectivity` and split on the `if`.
2. No-cut branch: `κ = ν - 1 ≥ 2` by `hν`, contradiction — so a cut exists.
3. `Nat.sInf_mem` gives a cut `S` with `|S| ≤ 1`.
   * `S = ∅`: `G` itself is disconnected, so no Hamilton cycle exists (a
     Hamilton cycle would make `G` connected).
   * `S = {v}`: apply `hamiltonian_toughness` with this `S`.  Its conclusion
     `ω(G - S) ≤ 1` contradicts `¬ (G.induce {v}ᶜ).Connected`, which gives
     `ω ≥ 2`.
4. ⚠ Step 3 needs a bridge between the two renderings of `G - S` — `IsVertexCut`
   uses `G.induce (↑S)ᶜ` while `hamiltonian_toughness` uses
   `((⊤ : G.Subgraph).deleteVerts ↑S).coe`.  These are isomorphic but not
   definitionally equal, so an explicit transport lemma is required.

## Status

`sorry`, and depends on `hamiltonian_toughness` (Theorem 4.2).
-/
theorem nonhamiltonian_of_not_two_connected (hν : 3 ≤ Fintype.card V)
    (h : ¬ (2 ≤ G.vertexConnectivity)) : ¬ G.IsHamiltonian := by
  sorry

/-- Ex 4.2.1(b): an unbalanced bipartite graph is nonhamiltonian.

## Book statement (§4.2, p. 68) — verbatim

> 4.2.1 Show that if either
>
> (a) $G$ is not 2-connected, or
> (b) $G$ is bipartite with bipartition $(X, Y)$ where $|X| \neq |Y|$,
> then $G$ is nonhamiltonian.

An exercise, so the book gives no proof.

## In Lean notation

Every edge crosses between `X` and `Y`, so a cycle alternates sides and uses
equally many vertices from each.  A Hamilton cycle uses *all* vertices, forcing
`|X| = |Y|`.

This is why the book's Herschel graph is nonhamiltonian:

> the Herschel graph (figure 4.2$b$) is nonhamiltonian, because it is bipartite
> and has an odd number of vertices.

(§4.2, p. 61.)  Equivalently, apply Theorem 4.2 with `S` the smaller side.

## Proof plan

Two routes:

* **Direct (recommended).**  Take a Hamilton cycle `c`.  Walking along `c`, the
  side alternates, so `c.support` restricted to `X` and to `Y` interleave; since
  `c` is closed its length is even and the two counts are equal.  Because `c` is
  Hamiltonian its support is all of `V`, so `|X| = |Y|`, contradicting `hne`.
  The alternation is an induction along the walk using `hb`.
* **Via Theorem 4.2.**  WLOG `|X| < |Y|`; take `S = X`.  Then `G - X` has all of
  `Y` isolated, so `ω(G - X) = |Y| > |X| = |S|`.  Shorter to state but needs the
  same `deleteVerts`-versus-`induce` bridge as part (a).

## Status

`sorry`.
-/
theorem nonhamiltonian_of_unbalanced_bipartite {X Y : Finset V}
    (hb : G.IsBipartiteWith ↑X ↑Y) (hne : X.card ≠ Y.card) : ¬ G.IsHamiltonian := by
  sorry

/-- Ex 4.2.3: a Hamilton path implies `ω(G − S) ≤ |S| + 1`.

## Book statement (§4.2, p. 68) — verbatim

> 4.2.3 Show that if $G$ has a Hamilton path then, for every proper subset $S$ of
> $V$, $\omega(G - S) \leq |S| + 1$.

An exercise, so the book gives no proof.

## In Lean notation

The path analogue of Theorem 4.2.  Deleting `k` vertices from a *path* breaks it
into at most `k + 1` pieces — one more than for a cycle, because a path has two
loose ends rather than being closed up.  The Hamilton path `P` is a spanning
subgraph of `G`, so `ω(G - S) ≤ ω(P - S) ≤ |S| + 1`.

The extra `+1` is the price of not closing the cycle, making the condition
weaker — as it must be, since a Hamilton path is weaker than a Hamilton cycle.

## Proof plan

Identical in shape to `hamiltonian_toughness`, with the cycle replaced by a path
and the bound loosened by one:
1. Obtain the Hamilton path `p` from `hG`.
2. `ω(p - S) ≤ |S| + 1` — deleting `|S|` interior vertices from a path leaves at
   most `|S| + 1` subpaths.
3. `ω(G - S) ≤ ω(p - S)` since `p` spans `G`.

Steps 2–3 are the same lemmas Theorem 4.2 needs, so both should be factored out
and shared rather than proved twice.

## Status

`sorry`.
-/
theorem hamiltonian_path_toughness
    (hG : ∃ (a b : V) (p : G.Walk a b), p.IsHamiltonian)
    (S : Finset V) (hS : S.Nonempty) (hSne : S ≠ Finset.univ) :
    Nat.card ((⊤ : G.Subgraph).deleteVerts ↑S).coe.ConnectedComponent ≤ S.card + 1 := by
  sorry

/-- Ex 4.2.4*: Chvátal's Hamilton-path degree condition (counting form).

## Book statement (§4.2, pp. 68–69) — verbatim

> 4.2.4\* Let $G$ be a nontrivial simple graph with degree sequence
> $(d_1, d_2, \ldots, d_\nu)$, where $d_1 \leq d_2 \leq \ldots \leq d_\nu$. Show
> that if there is no value of $m$ less than $(\nu+1)/2$ for which $d_m < m$ and
> $d_{\nu-m+1} < \nu - m$, then $G$ has a Hamilton path. (V. Chvátal)

A starred exercise, so the book gives no proof.

## In Lean notation

The Hamilton-*path* counterpart of Theorem 4.5, with thresholds shifted by one.
Formalised in counting form, exactly as Theorem 4.5 is — see the note there on
why indexing the sorted sequence is avoided.

Note the strict `d_m < m` here versus `d_m ≤ m` in Theorem 4.5; the `hcond`
filters use `<` accordingly.

## Proof plan

The standard route reduces to Theorem 4.5 by a **cone construction**:
1. Form `G⁺` on `Option V` (or `V ⊕ Unit`), joining the new vertex to every
   vertex of `G`.  In this file's vocabulary that is `G.join (⊥ : SimpleGraph Unit)`.
2. A Hamilton *cycle* of `G⁺` corresponds exactly to a Hamilton *path* of `G`:
   delete the new vertex and its two incident cycle edges.
3. Degrees in `G⁺`: `d⁺(v) = d(v) + 1` for `v ∈ V`, and `d⁺(new) = ν`.  Feeding
   these into Theorem 4.5's hypothesis at `ν + 1` is precisely the shift that
   turns this exercise's condition into that one.
4. Apply `chvatal_hamiltonian` to `G⁺` and pull the cycle back.

Step 2 is the fiddly direction — mapping a cycle in `G⁺` back to a walk in `G`
requires a `Walk` transport across the carrier change.

## Status

`sorry`.
-/
theorem chvatal_hamiltonian_path (hν : 2 ≤ Fintype.card V)
    (hcond : ∀ m : ℕ, 1 ≤ m → 2 * m < Fintype.card V + 1 →
      ¬ (m ≤ (Finset.univ.filter fun v => G.degree v < m).card ∧
         Fintype.card V - m + 1 ≤
           (Finset.univ.filter fun v => G.degree v < Fintype.card V - m).card)) :
    ∃ (a b : V) (p : G.Walk a b), p.IsHamiltonian := by
  sorry

/-- Ex 4.2.5: a self-complementary graph has a Hamilton path (Clapham).

## Book statement (§4.2, p. 69) — verbatim

> **4.2.5** (a) Let $G$ be a simple graph with degree sequence
> $(d_1, d_2, \ldots, d_\nu)$ and let $G^c$ have degree sequence
> $(d_1', d_2', \ldots, d_\nu')$ where $d_1 \le d_2 \le \ldots \le d_\nu$ and
> $d_1' \le d_2' \le \ldots \le d_\nu'$. Show that if $d_m \ge d_m'$ for all
> $m \le \nu/2$, then $G$ has a Hamilton path.
>
> (b) Deduce that if $G$ is self-complementary, then $G$ has a Hamilton path.
> (C. R. J. Clapham)

An exercise, so the book gives no proof.

## In Lean notation

Only part (b) is formalised — part (a) has no separate declaration in this file.

Part (b) from part (a): if `G ≅ Gᶜ` the two sorted degree sequences are
*identical*, so `d_m ≥ d_m'` holds trivially at every index.

Recall from exercise 1.2.11(b) that self-complementary graphs exist only when
`ν ≡ 0` or `1 (mod 4)`.

## Proof plan

⚠ Since part (a) is not stated separately, this proof must either prove it inline
or go directly. Directly:
1. From `h : Nonempty (G ≃g Gᶜ)`, `G` and `Gᶜ` have equal degree sequences
   (`Iso` preserves degrees), so `d_m = d_m'` for every `m`.
2. `d_m + d_m' = ν - 1` for each `m`, since `d_{Gᶜ}(v) = ν - 1 - d_G(v)` and the
   sortings are reverse to one another. Hence `2 d_m = ν - 1`, so every vertex
   has degree `(ν-1)/2` — i.e. `G` is regular of degree `(ν-1)/2`.
3. That is well above the Chvátal path threshold, so `chvatal_hamiltonian_path`
   applies; alternatively `ν ≤ 2δ + 1` is enough for a Hamilton path directly.

## Status

`sorry`, and depends on `chvatal_hamiltonian_path` unless step 3 goes direct.
Part (a) is now stated separately as `hamiltonian_path_of_degree_dominates_compl`
directly below, so this may be derived from it rather than proved inline.
-/
theorem hamiltonian_path_of_self_complementary (h : Nonempty (G ≃g Gᶜ)) :
    ∃ (a b : V) (p : G.Walk a b), p.IsHamiltonian := by
  sorry

/-- Ex 4.2.5(a) (Clapham): if `G` dominates `Gᶜ` on the lower half of the sorted
degree sequence, `G` has a Hamilton path.

## Book statement (§4.2, p. 61) — verbatim

> **4.2.5** (a) Let $G$ be a simple graph with degree sequence
> $(d_1, d_2, \ldots, d_\nu)$ and let $G^c$ have degree sequence
> $(d_1', d_2', \ldots, d_\nu')$ where $d_1 \le d_2 \le \ldots \le d_\nu$ and
> $d_1' \le d_2' \le \ldots \le d_\nu'$. Show that if $d_m \ge d_m'$ for all
> $m \le \nu/2$, then $G$ has a Hamilton path.

An exercise, so the book gives no proof.

## Provenance

**Restored transcription.**  This file previously formalised only part (b)
(`hamiltonian_path_of_self_complementary`), even though the book deduces (b) *from*
(a) — so (a) was a hidden prerequisite with no declaration.  The triage
(`log/graphtheory-EXERCISE_TRIAGE.md` §A.3) recorded this as a fidelity gap and
recommended stating (a).  Nothing here is invented: the statement is the book's
own, quoted above.

## In Lean notation

The two sorted degree sequences are rendered the way `chvatal_hamiltonian_path`
renders its sequence — via a sorting equiv `σ` on `Fin ν` making the degrees
`Antitone`/`Monotone` — rather than as raw lists, so the two conditions in this file
are stated in the same idiom and can share lemmas.

`m ≤ ν/2` is written `2 * m ≤ ν` to avoid ℕ-division.

## Proof plan

1. Sort both degree sequences; `hdom` compares them index by index on the lower half.
2. `d_m + d'_{ν+1-m} = ν - 1` for every `m`, since `d_{Gᶜ}(v) = ν - 1 - d_G(v)` and
   sorting `Gᶜ` ascending reverses the order of the `G`-sorting.
3. Feed the resulting inequality into the Chvátal path condition and apply
   `chvatal_hamiltonian_path`.

⚠ Step 2 is the whole content, and is where the two sortings must be related; it is
the step the book leaves to the reader.

## Status

`sorry`.  Part (b) above should be derived from this once it is filled.
-/
theorem hamiltonian_path_of_degree_dominates_compl
    (σ τ : Fin (Fintype.card V) ≃ V)
    (hσ : Monotone fun i => G.degree (σ i))
    (hτ : Monotone fun i => Gᶜ.degree (τ i))
    (hdom : ∀ m : Fin (Fintype.card V), 2 * (m : ℕ) ≤ Fintype.card V →
      Gᶜ.degree (τ m) ≤ G.degree (σ m)) :
    ∃ (a b : V) (p : G.Walk a b), p.IsHamiltonian := by
  sorry

/-- Ex 4.2.8: Erdős' edge bound `ν ≥ 6δ`, `ε > C(ν−δ,2) + δ²` ⇒ hamiltonian.

## Book statement (§4.2, p. 69) — verbatim

> **4.2.8** Show that if $G$ is simple with $\nu \ge 6\delta$ and
> $\varepsilon > \binom{\nu-\delta}{2} + \delta^2$, then $G$ is hamiltonian.
> (P. Erdös)

An exercise, so the book gives no proof.

## In Lean notation

Corollary 4.6 gives a sufficient edge count taking no account of the minimum
degree.  Erdős' refinement: when `δ` is known and small relative to `ν`, a weaker
count suffices — `C(ν-δ, 2) + δ²` rather than `C(ν-1, 2) + 1`.

The shape of the bound reflects the extremal configuration: a clique on `ν - δ`
vertices with `δ` low-degree vertices attached, the densest way to be
nonhamiltonian while holding the minimum degree at `δ`.  `ν ≥ 6δ` keeps `δ`
genuinely small.

## Proof plan

Substantially harder than Corollary 4.6 and not a direct consequence of it.  The
standard argument:
1. Assume nonhamiltonian; take a longest path and apply a rotation/extension
   argument to bound the number of vertices of degree `< ν/2`.
2. Split the edge count between the high-degree "clique-like" part and the `δ`
   low-degree vertices, bounding each separately.
3. `ν ≥ 6δ` is what makes the two bounds combine to contradict `hε`.

No shortcut through `chvatal_degree_majorised` is available, because that gives a
bound in terms of `m` rather than `δ`.

## Status

`sorry`.  One of the harder exercises in the chapter.
-/
theorem erdos_hamiltonian (hν : 6 * G.minDegree ≤ Fintype.card V)
    (hε : (Fintype.card V - G.minDegree).choose 2 + G.minDegree ^ 2 < G.edgeFinset.card) :
    G.IsHamiltonian := by
  sorry

/-- Ex 4.2.9*: connected with `ν > 2δ` ⇒ a path of length ≥ `2δ` (Dirac).

## Book statement (§4.2, p. 69) — verbatim

> **4.2.9\*** Show that if $G$ is a connected graph with $\nu > 2\delta$, then $G$
> has a path of length at least $2\delta$. (G. A. Dirac)
>
> (Dirac, 1952 has also shown that if $G$ is a 2-connected simple graph with
> $\nu \ge 2\delta$, then $G$ has a cycle of length at least $2\delta$.)

A starred exercise, so the book gives no proof.

## In Lean notation

Exercise 1.6.3 already gives a path of length `δ` from the minimum degree alone;
Dirac's sharpening doubles that, at the cost of connectivity and `ν > 2δ`.

## Proof plan

1. Take a longest path `p` in `G` (exists since `V` is finite — maximise
   `p.length` over `p.IsPath`).
2. By maximality, every neighbour of either endpoint lies on `p`; otherwise `p`
   extends.
3. If `p.length < 2δ`, the two endpoints each have `≥ δ` neighbours among fewer
   than `2δ` path vertices, so their neighbourhoods overlap — which yields a
   cycle through all of `p`, and then connectivity plus `ν > 2δ` lets that cycle
   be extended to a longer path, contradicting maximality.

Step 3 is the crux and is where `ν > 2δ` is consumed.

## The parenthetical remark

The bracketed cycle version — 2-connected, `ν ≥ 2δ`, cycle of length `≥ 2δ` — is
**stated but not proved** in the chapter.  It is what exercise 4.2.10 relies on;
see the warning there.  It is not stated in this file either.

## Status

`sorry`.
-/
theorem long_path_of_order_gt_two_minDegree (hconn : G.Connected)
    (h : 2 * G.minDegree < Fintype.card V) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ 2 * G.minDegree ≤ p.length := by
  sorry

/-- Ex 4.2.10: a `2k`-regular graph on `4k+1` vertices is hamiltonian (Nash-Williams).
⚠ Its proof depends on the chapter's *unproved* parenthetical remark after Ex 4.2.9.

## Book statement (§4.2, p. 69) — verbatim

> **4.2.10** Using the remark to exercise 4.2.9, show that every $2k$-regular
> simple graph on $4k+1$ vertices is hamiltonian ($k \ge 1$).
> (C. St. J. A. Nash-Williams)

An exercise, so the book gives no proof.

## In Lean notation

Such a graph has `δ = Δ = 2k` and `ν = 4k + 1 = 2δ + 1`, one vertex above the
threshold `ν ≥ 2δ` of Dirac's cycle remark.  That remark yields a cycle of length
at least `2δ = 4k` — missing at most one vertex — and regularity plus parity then
force the cycle to pick up the last vertex too.

⚠ The Lean signature omits the book's `k ≥ 1`.  At `k = 0` the statement reads
"every `0`-regular graph on `1` vertex is hamiltonian", which is false in
Mathlib: a Hamilton cycle needs length `≥ 3`, so the one-vertex graph is not
`IsHamiltonian`.  The hypothesis `1 ≤ k` must be added.

## Proof plan

1. First state and prove the parenthetical remark of exercise 4.2.9 — 2-connected
   plus `ν ≥ 2δ` gives a cycle of length `≥ 2δ`.  **It is stated but not proved
   in the chapter, and is not stated in this file at all**, so it must be added
   before this exercise is reachable.
2. Show a `2k`-regular graph on `4k+1` vertices is 2-connected (regularity plus
   the order bound rules out cut vertices).
3. Get a cycle `c` of length `≥ 4k`, so `c` misses at most one vertex `x`.
4. If `c` misses `x`, use `d(x) = 2k` and the cycle's structure to find two
   consecutive cycle vertices both adjacent to `x`, then splice `x` in.

## Status

`sorry`, still blocked on step 1 (an unproved book remark).  ✅ **Hypothesis
repaired** — `hk : 1 ≤ k` added, restoring the book's `(k \ge 1)`.  Without it the
statement is **false** at `k = 0`, where it claims the one-vertex graph is
hamiltonian; Mathlib's `IsHamiltonian` needs a cycle of length `≥ 3`.
-/
theorem nash_williams_regular_hamiltonian (k : ℕ) (hk : 1 ≤ k)
    (hreg : G.IsRegularOfDegree (2 * k)) (hcard : Fintype.card V = 4 * k + 1) :
    G.IsHamiltonian := by
  sorry

/-- Ex 4.2.11(a): a Hamilton-connected graph satisfies `3ν + 1 ≤ 2ε` (Moon).

## Book statement (§4.2, p. 69) — verbatim

> **4.2.11** $G$ is *Hamilton-connected* if every two vertices of $G$ are
> connected by a Hamilton path.
>
> (a) Show that if $G$ is Hamilton-connected and $\nu \ge 4$, then
> $\varepsilon \ge [\frac{1}{2}(3\nu+1)]$.

An exercise, so the book gives no proof.

## In Lean notation

Hamilton-connectedness demands a spanning path between *every* pair, forcing many
edges.  Every vertex must have degree at least `3`: a degree-`2` vertex has both
its edges forced into any spanning path through it as an interior vertex, leaving
no way to make it an endpoint of a spanning path to a third vertex.  Summing
`d(v) ≥ 3` and applying handshaking gives `2ε ≥ 3ν`, and a parity refinement
pushes this to `2ε ≥ 3ν + 1`.

Formalised as `3ν + 1 ≤ 2ε` to stay in the natural numbers and avoid the ceiling.

⚠ The Lean signature omits the book's `ν ≥ 4`.  It is needed: for `ν = 3`,
`⊤` on three vertices is Hamilton-connected with `ε = 3`, but `3ν + 1 = 10 > 6 = 2ε`.
So the statement as written is **false at `ν = 3`** and `4 ≤ Fintype.card V` must
be added.

## Proof plan

1. Show `∀ v, 3 ≤ G.degree v`, using `ν ≥ 4` and the degree-`2` argument above.
2. `3ν = ∑ 3 ≤ ∑ d(v) = 2ε` by `Finset.sum_le_sum` and handshaking.
3. Parity: `2ε` is even, so if `3ν` is odd then `3ν < 2ε` already gives
   `3ν + 1 ≤ 2ε`.  If `3ν` is even, rule out equality — `2ε = 3ν` would make `G`
   exactly 3-regular, and a 3-regular graph is not Hamilton-connected (a spanning
   path between two adjacent vertices would leave a degree-3 vertex with all
   three edges used).

## Status

`sorry`.  ✅ **Hypothesis repaired** — `hν : 4 ≤ Fintype.card V` added, restoring the
book's `\nu \ge 4`.  Without it the statement is **false at `ν = 3`**, as the
paragraph above works out.
-/
theorem hamiltonConnected_edge_bound (hν : 4 ≤ Fintype.card V)
    (h : G.IsHamiltonConnected) :
    3 * Fintype.card V + 1 ≤ 2 * G.edgeFinset.card := by
  sorry

-- Ex 4.2.12: the Petersen graph is hypohamiltonian.
-- NOTE: the outline provides no signature and flags the Petersen graph itself as "to build"
-- (ideally the Kneser graph `K(5,2)`). It is a placeholder `def … := sorry` here; the
-- statement below is well-typed but quantifies over that placeholder until it is built.
/-- The Petersen graph (placeholder carrier `Fin 10`; construction deferred).

## Book context (§4.2, figure 4.4, p. 63)

The book introduces the Petersen graph only by a figure, so there is no
definitional text to quote.  It is the chapter's standing counterexample:

> for instance, the Petersen graph (figure 4.4) is nonhamiltonian, but one cannot
> deduce this by using theorem 4.2.

(§4.2, p. 62.)

## In Lean notation

The 3-regular graph on ten vertices, most conveniently the Kneser graph `K(5,2)`:
vertices are the ten 2-element subsets of a 5-element set, adjacent exactly when
disjoint.  Drawn conventionally, an outer 5-cycle joined by spokes to an inner
pentagram.

It has girth five and is 3-regular, meeting the bound of exercise 1.7.4(b) with
equality (`k² + 1 = 10` vertices).

## Status

`sorry` — the construction is **not** written.  As a `def`, this `sorry` makes
`petersenGraph` an opaque constant with no defining equations, so
`petersen_isHypohamiltonian` below is not merely unproved but **unprovable** as
it stands.  Filling this definition is a prerequisite.

Two reasonable carriers:
* `Fin 10` with an explicit adjacency table — matches the current signature, and
  makes `decide` viable for the finite checks;
* `{s : Finset (Fin 5) // s.card = 2}` with `Adj s t := Disjoint s.1 t.1` — the
  Kneser description, which makes vertex-transitivity available and so cuts the
  ten cases of Ex 4.2.12 down to one.

The second is better for proving hypohamiltonicity; the first is better for
`decide`.
-/
def petersenGraph : SimpleGraph (Fin 10) := sorry

end SimpleGraph
