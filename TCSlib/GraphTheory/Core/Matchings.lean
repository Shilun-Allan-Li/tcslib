import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.UniversalVerts
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Bondy & Murty, *Graph Theory with Applications* — Chapter 5: Matchings

Sorry-skeleton extracted from `papers/bondy-murty-ch5-matchings.md`.

Every proof body is `sorry`; this file is a scaffold for sorry-driven development
(fill one stub at a time, `lake build` after each).

Mathlib already provides `Subgraph.IsMatching`, `Subgraph.IsPerfectMatching`,
`SimpleGraph.tutte`, Hall (`Finset.all_card_le_biUnion_card_iff_exists_injective`),
Birkhoff (`exists_eq_sum_perm_of_mem_doublyStochastic`), `oddComponents`,
`IsTutteViolator`, `IsBipartiteWith`, `IsMatchingFree` — those are referenced, not
redefined.  The outline's `import TCSlib.*` lines refer to repo files that do not
exist and have been dropped; `IsEdgeCut`/`edgeConnectivity` (needed only by Ex 5.3.2)
are defined locally, mirroring `Connectivity.lean`.

Items marked DROP / N/A in the outline (Ex 5.1.5b, Ex 5.3.5a, Ex 5.4.1, Ex 5.5.1,
Ex 5.2.7, Ex 5.3.1, the Hungarian/Kuhn–Munkres procedures, `IsAlternatingTree`) are
omitted with a note.
-/

open scoped Pointwise

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Key Definitions (the `⚠ MISSING`, NEEDED-TO-STATE items) -/

/-- A **maximum matching**: a matching no larger than which exists.
⚠ MISSING from Mathlib (no matching-number notion). Honest def.

## Book definition (§5.1, p. 78) — verbatim

> A subset $M$ of $E$ is called a *matching* in $G$ if its elements are links and
> no two are adjacent in $G$; the two ends of an edge in $M$ are said to be
> *matched under $M$*. A matching $M$ *saturates* a vertex $v$, and $v$ is said to
> be *$M$-saturated*, if some edge of $M$ is incident with $v$; otherwise, $v$ is
> *$M$-unsaturated*. If every vertex of $G$ is $M$-saturated, the matching $M$ is
> *perfect*. $M$ is a *maximum matching* if $G$ has no matching $M'$ with
> $|M'| > |M|$; clearly, every perfect matching is maximum.

## In Lean notation

Mathlib supplies "matching" (`Subgraph.IsMatching`), "saturates"
(`v ∈ M.verts`) and "perfect" (`Subgraph.IsPerfectMatching`), but has **no
matching-number notion**, so maximality has to be said by hand:

    M.IsMatching ∧ ∀ M', M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard

This is a *global* maximum, not a maximal matching (one admitting no extension).
The two genuinely differ, and Berge's Theorem 5.1 is exactly the tool that
certifies the global property from a local check.
-/
def Subgraph.IsMaximumMatching {V : Type*} {G : SimpleGraph V} (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard

/-- `M`-**alternating walk**: consecutive edges alternate in/out of `M`.
⚠ MISSING.  NOTE: `SimpleGraph.IsAlternating` (`Matching.lean:539`) is a *graph-level*
relation between two graphs and is NOT this.

## Book definition (§5.1, p. 78) — verbatim

> Let $M$ be a matching in $G$. An *$M$-alternating path* in $G$ is a path whose
> edges are alternately in $E \backslash M$ and $M$. For example, the path
> $v_5 v_8 v_1 v_7 v_6$ in the graph of figure 5.1$a$ is an $M$-alternating path.

## In Lean notation

Walk along the graph using a matching edge, then a non-matching edge, then a
matching edge, and so on.  Rendered as a chain condition on consecutive edges:

    List.IsChain (fun e f => e ∈ M.edgeSet ↔ f ∉ M.edgeSet) p.edges

⚠ Mathlib's `SimpleGraph.IsAlternating` (`Matching.lean`) is a *graph-level*
relation between two graphs and is **not** this notion; do not reach for it.

Note the definition is on a `Walk`, not a `Path` — the book's "path" is imposed
separately in `IsAugmenting` below via `p.IsPath`.

## Why it matters

Alternating paths are the mechanism by which a matching improves: swapping which
edges along such a path belong to `M` keeps `M` a matching.
-/
def Walk.IsAlternatingWalk {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (M : G.Subgraph) {u v : V} (p : G.Walk u v) : Prop :=
  List.IsChain (fun e f => e ∈ M.edgeSet ↔ f ∉ M.edgeSet) p.edges

/-- `M`-**augmenting path**: alternating, both ends `M`-unsaturated.
⚠ `u ≠ v` is LOAD-BEARING (else `Walk.nil` qualifies and Berge is false).

## Book definition (§5.1, p. 78) — verbatim

> An *$M$-augmenting path* is an $M$-alternating path whose origin and terminus
> are $M$-unsaturated.

## In Lean notation

An alternating path both of whose endpoints are still unmatched.  Such a path has
odd length and begins and ends with non-matching edges, so it holds one more
non-`M` edge than `M` edge.  Flipping the roles along it — discarding its
`M`-edges, adopting its non-`M`-edges — yields a matching one edge *larger*,
which is why it is called augmenting.

⚠ The conjunct `u ≠ v` is **load-bearing** and has no counterpart in the book's
wording.  Without it `Walk.nil` at an `M`-unsaturated vertex would satisfy every
other clause vacuously, so *every* non-perfect matching would admit an
"augmenting path" and Berge's theorem would be false in the (⇐) direction.  The
book gets this for free because a path in its sense has at least one edge.
-/
def Walk.IsAugmenting {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (M : G.Subgraph) {u v : V} (p : G.Walk u v) : Prop :=
  u ≠ v ∧ p.IsPath ∧ p.IsAlternatingWalk M ∧ u ∉ M.verts ∧ v ∉ M.verts

/-- A (vertex) **covering** `K`: every edge has an end in `K`.
⚠ MISSING — no vertex-cover notion exists anywhere in Mathlib.

## Book definition (§5.2, p. 81) — verbatim

> A *covering* of a graph $G$ is a subset $K$ of $V$ such that every edge of $G$
> has at least one end in $K$.

## In Lean notation

A set of vertices that between them "watch" every edge:
`∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K`.

⚠ No vertex-cover notion exists anywhere in Mathlib, so this is defined here from
scratch.

## Why it matters

Coverings are dual to matchings.  The book records the easy half at (5.5):

> If $K$ is a covering of $G$, and $M$ is a matching of $G$, then $K$ contains at
> least one end of each of the edges in $M$. Thus, for any matching $M$ and any
> covering $K$, $|M| \le |K|$.

König's Theorem 5.3 says the two optima coincide for bipartite graphs — and, as
the book stresses with figure 5.4, *not* in general.
-/
def IsCovering {V : Type*} (G : SimpleGraph V) (K : Set V) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → u ∈ K ∨ v ∈ K

/-- A **minimum covering**. ⚠ MISSING. Honest def.

## Book definition (§5.2, p. 81) — verbatim

> A covering $K$ is a *minimum covering* if $G$ has no covering $K'$ with
> $|K'| < |K|$ (see figure 5.4).

## In Lean notation

Watch every edge using as few vertices as possible.  As with
`Subgraph.IsMaximumMatching`, minimality is spelled out by hand since Mathlib has
no covering-number notion.
-/
def IsMinimumCovering {V : Type*} (G : SimpleGraph V) (K : Set V) : Prop :=
  G.IsCovering K ∧ ∀ K' : Set V, G.IsCovering K' → K.ncard ≤ K'.ncard

/-- A `k`-**factor**: a `k`-regular spanning subgraph.  ⚠ MISSING.
NOTE: the outline states `∀ v, H.degree v = k`; we use `(H.neighborSet v).ncard = k`
(equal to `Subgraph.degree`) to avoid `Fintype`/`DecidableRel` instance juggling.

## Book definition (exercise 5.1.5, p. 79) — verbatim

> **5.1.5** A $k$-*factor* of $G$ is a $k$-regular spanning subgraph of $G$, and
> $G$ is $k$-*factorable* if there are edge-disjoint $k$-factors
> $H_1, H_2, \ldots, H_n$ such that $G = H_1 \cup H_2 \cup \ldots \cup H_n$.

## In Lean notation

Keep every vertex, and select edges so each vertex retains exactly `k`.  A
`1`-factor is precisely a perfect matching; a `2`-factor is a spanning union of
disjoint cycles.

Degree is written `(H.neighborSet v).ncard` rather than `H.degree v` — equal in
value, but avoiding the `Fintype`/`DecidableRel` instance juggling that
`Subgraph.degree` would drag in on every use.
-/
def Subgraph.IsKFactor {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) (k : ℕ) : Prop :=
  H.IsSpanning ∧ ∀ v, (H.neighborSet v).ncard = k

/-- `G` is `k`-**factorable**: it decomposes into edge-disjoint `k`-factors. ⚠ MISSING.

## Book definition (exercise 5.1.5, p. 79) — verbatim

> $G$ is $k$-*factorable* if there are edge-disjoint $k$-factors
> $H_1, H_2, \ldots, H_n$ such that $G = H_1 \cup H_2 \cup \ldots \cup H_n$.

## In Lean notation

The edges of `G` partition into groups, each a `k`-regular spanning subgraph.
The book's `G = H₁ ∪ … ∪ H_n` becomes `(⨆ i, H i) = ⊤` in the `Subgraph` lattice,
where `⊤` is `G` viewed as a subgraph of itself.

Being `1`-factorable means the edges split into perfect matchings: `K_{n,n}` and
`K_{2n}` are (exercise 5.1.5(a)(i)), the Petersen graph is not
(exercise 5.1.5(a)(ii)).

## Connection to chapter 6

`1`-factorability is exactly proper edge colouring with `Δ` colours: each factor
is a colour class.  So exercise 5.1.5(a)(ii) is the statement that the Petersen
graph has chromatic index `4`, which reappears in `EdgeColourings.lean`.
-/
def IsKFactorable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (n : ℕ) (H : Fin n → G.Subgraph), (∀ i, (H i).IsKFactor k) ∧
    (∀ i j, i ≠ j → Disjoint (H i).edgeSet (H j).edgeSet) ∧
    (⨆ i, H i) = ⊤

/-- The `k`-**cube** `Q_k`.  ⚠ MISSING (0 hits). Honest def: adjacency = differ in one coord.

## Book definition (exercise 1.2.10)

> The $k$-cube is the graph whose vertices are the ordered $k$-tuples of $0$s and
> $1$s, two vertices being joined if and only if they differ in exactly one
> coordinate.

Defined in chapter 1; chapter 5 uses it only in exercise 5.1.1(a).

## In Lean notation

The corners and edges of a `k`-dimensional cube: `k`-regular, bipartite (split by
the parity of the number of `1`s), `2^k` vertices, `k·2^{k-1}` edges.

Adjacency is the book's condition literally: `∃! i, x i ≠ y i`.

⚠ Note this file defines `cube` directly as a structure, whereas
`GraphsAndSubgraphs.lean` defines the same graph as
`SimpleGraph.fromRel (fun x y => ∃! i, x i ≠ y i)`.  The two are equal but not
definitionally so, and neither imports the other.

## Status

Fully defined — `symm` and `loopless` were proved this session (previously `sorry`
proof fields; `Adj` always had content).
-/
def cube (k : ℕ) : SimpleGraph (Fin k → Bool) where
  Adj x y := ∃! i, x i ≠ y i
  symm := by
    rintro x y ⟨i, hi, huniq⟩
    exact ⟨i, Ne.symm hi, fun j hj => huniq j (Ne.symm hj)⟩
  loopless := by
    rintro x ⟨i, hi, -⟩
    exact hi rfl

/-- The **Petersen graph** as the Kneser graph on 2-subsets of `Fin 5`.  ⚠ MISSING (0 hits).

## Book context (figure 4.4; exercise 5.1.5(a)(ii), p. 79)

The book introduces the Petersen graph by figure only, so there is no
definitional text to quote.  Chapter 5 uses it in:

> (ii) the Petersen graph is not 1-factorable.

## In Lean notation

Realised as the Kneser graph `K(5,2)`: vertices are the ten 2-element subsets of
`Fin 5`, adjacent exactly when disjoint.  Carrier
`{s : Finset (Fin 5) // s.card = 2}`.

✅ This is the *better* of the two carriers discussed on `EulerHamilton.lean`'s
`petersenGraph`, and unlike that one it is **actually defined here** — that file's
version is `def petersenGraph : SimpleGraph (Fin 10) := sorry`, an opaque
constant.  Anything needing a usable Petersen graph should prefer this one.

⚠ The two are unrelated declarations in different namespaces with the same name;
neither file imports the other.

## Why it matters here

Although the Petersen graph is `3`-regular and bridgeless — so Corollary 5.4
gives it a perfect matching — its edges cannot be partitioned into three perfect
matchings.  It therefore separates "has a 1-factor" from "is 1-factorable".

## Status

Fully defined — `symm` and `loopless` were proved this session (previously `sorry`
proof fields).
-/
def petersenGraph : SimpleGraph {s : Finset (Fin 5) // s.card = 2} where
  Adj a b := Disjoint (a : Finset (Fin 5)) (b : Finset (Fin 5))
  symm := fun _ _ h => h.symm
  loopless := by
    rintro ⟨a, ha⟩ h
    have : (a : Finset (Fin 5)) = ⊥ := disjoint_self.mp h
    simp [Finset.bot_eq_empty] at this
    simp [this] at ha

/-- The `m × n` **grid graph**.  ⚠ MISSING. Honest def.

## Book context (exercise 5.2.1, p. 83) — verbatim

> **5.2.1** Show that it is impossible, using $1 \times 2$ rectangles, to exactly
> cover an $8 \times 8$ square from which two opposite $1 \times 1$ corner squares
> have been removed.

The book gives no graph-theoretic definition here; modelling the board as a graph
is the formaliser's step.

## In Lean notation

Vertices are the squares of an `m × n` board, adjacent when they share a side.
A perfect matching is exactly a tiling by `1 × 2` dominoes, since each domino
covers precisely one side-adjacent pair.

Adjacency is spelled out coordinatewise: same row and columns differing by one,
or same column and rows differing by one.  Written on `ℕ` values (`p.2.val + 1 =
q.2.val`) rather than on `Fin` arithmetic, which would wrap around and wrongly
join the last column to the first.

## Status

Fully defined — `symm` and `loopless` were proved this session (previously `sorry`
proof fields).
-/
def gridGraph (m n : ℕ) : SimpleGraph (Fin m × Fin n) where
  Adj p q := (p.1 = q.1 ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
             (p.2 = q.2 ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))
  symm := by
    rintro p q (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩)
    · exact Or.inl ⟨h1.symm, Or.inr h2⟩
    · exact Or.inl ⟨h1.symm, Or.inl h2⟩
    · exact Or.inr ⟨h1.symm, Or.inr h2⟩
    · exact Or.inr ⟨h1.symm, Or.inl h2⟩
  loopless := by
    rintro p (⟨-, h | h⟩ | ⟨-, h | h⟩) <;> omega

/-- Local edge-cut predicate (repo `Connectivity.lean` idiom); the outline's
`import TCSlib.GraphTheory.Connectivity.Defs` is unavailable, so it is inlined for Ex 5.3.2.

## Book definition (§3.1, p. 50) — verbatim

> Recall that an edge cut of $G$ is a subset of $E$ of the form $[S, \bar{S}]$,
> where $S$ is a nonempty proper subset of $V$. A *$k$-edge cut* is an edge cut of
> $k$ elements.

## In Lean notation

Taken in its operative form — a set of edges whose removal disconnects `G` — as
in `Connectivity.lean`; see there for why the two agree for minimisation
purposes.

⚠ Duplicated rather than imported: the outline's
`import TCSlib.GraphTheory.Connectivity.Defs` refers to a file that does not
exist, and this file does not depend on `Connectivity.lean`.

## Where it is used

Exercise 5.3.2 only, which generalises Petersen's Corollary 5.4 from bridgeless
cubic graphs to `(k-1)`-edge-connected `k`-regular graphs.
-/
def IsEdgeCut (G : SimpleGraph V) (F : Finset (Sym2 V)) : Prop :=
  (↑F : Set (Sym2 V)) ⊆ G.edgeSet ∧ ¬ (G.deleteEdges (↑F : Set (Sym2 V))).Connected

/-- Local edge connectivity `κ'(G)` (`sInf ∅ = 0`).

## Book definition (§3.1, p. 50) — verbatim

> we then define the *edge connectivity* $\kappa'(G)$ of $G$ to be the minimum
> $k$ for which $G$ has a $k$-edge cut. If $G$ is trivial, $\kappa'(G)$ is defined
> to be zero.

## In Lean notation

`sInf` over the sizes of edge cuts, with `Nat.sInf ∅ = 0` supplying the book's
trivial case automatically — identical to `Connectivity.lean`'s version.

⚠ Duplicated, as with `IsEdgeCut` above.

## Where it is used

Exercise 5.3.2 only.
-/
noncomputable def edgeConnectivity (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ F : Finset (Sym2 V), G.IsEdgeCut F ∧ F.card = n}

/-! ## Theorem 5.1: Berge's augmenting-path criterion (Berge, 1957) — grade 82 -/

/-- Thm 5.1 (Berge): a matching is maximum iff there is no augmenting path.

## Book statement (§5.1, p. 78) — verbatim

> **Theorem 5.1** (Berge, 1957)  A matching $M$ in $G$ is a maximum matching if
> and only if $G$ contains no $M$-augmenting path.

## Book proof (§5.1, pp. 78–79) — verbatim

> Let $M$ be a matching in $G$, and suppose that $G$ contains an $M$-augmenting
> path $v_0 v_1 \ldots v_{2m+1}$. Define $M' \subseteq E$ by
> $$M' = (M \backslash \{v_1 v_2, v_3 v_4, \ldots, v_{2m-1} v_{2m}\}) \cup \{v_0 v_1, v_2 v_3, \ldots, v_{2m} v_{2m+1}\}$$
> Then $M'$ is a matching in $G$, and $|M'| = |M| + 1$. Thus $M$ is not a maximum
> matching.
>
> Conversely, suppose that $M$ is not a maximum matching, and let $M'$ be a
> maximum matching in $G$. Then
> $$|M'| > |M| \tag{5.1}$$
> Set $H = G[M \, \Delta M']$, where $M \, \Delta M'$ denotes the symmetric
> difference of $M$ and $M'$ (see figure 5.2).
>
> Each vertex of $H$ has degree either one or two in $H$, since it can be incident
> with at most one edge of $M$ and one edge of $M'$. Thus each component of $H$ is
> either an even cycle with edges alternately in $M$ and $M'$, or else a path with
> edges alternately in $M$ and $M'$. By (5.1), $H$ contains more edges of $M'$
> than of $M$, and therefore some path component $P$ of $H$ must start and end
> with edges of $M'$. The origin and terminus of $P$, being $M'$-saturated in $H$,
> are $M$-unsaturated in $G$. Thus $P$ is an $M$-augmenting path in $G$.

## In Lean notation

Both directions are stated contrapositively relative to the book's phrasing: the
Lean `↔` has "no augmenting path" on the right, so the book's first paragraph
proves (⇒) by contraposition and its second proves (⇐) by contraposition.

Augmenting paths are simultaneously the certificate of non-maximality and the
means of improvement — which is what makes the Hungarian method of §5.4 work.

## Proof plan

(⇒) Given an augmenting path `p`, build `M'` as the symmetric difference
`M Δ p.edges`:
1. Show `M'` is a matching — each vertex on `p` keeps exactly one incident
   `M'`-edge, and off `p` nothing changes.
2. `|M'| = |M| + 1` — `p` alternates starting and ending outside `M`, so it
   carries `m + 1` non-`M` edges against `m` `M`-edges.
3. Contradict `M.IsMaximumMatching` applied to `M'`.

(⇐) Given `M` not maximum, take `M'` maximum and analyse `H = M Δ M'`:
4. Every `H`-degree is `≤ 2` (one edge from each matching), so components are
   paths or cycles — this needs a "degree ≤ 2 implies path-or-cycle" structure
   structure lemma **Mathlib does not have**, and it is the bulk of the work.
5. Cycles alternate, hence are even and contribute equally to both matchings;
   since `|M'| > |M|`, some path component starts and ends with `M'`-edges.
6. That component is `M`-augmenting.

## Status

`sorry`.  Step 4 is the real obstacle — the component-structure lemma is
reusable and worth stating separately.  This is the load-bearing theorem of §5.1
and Hall's theorem below depends on it.
-/
theorem berge_maximum_matching
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMatching) :
    M.IsMaximumMatching ↔ ¬ ∃ (u v : V) (p : G.Walk u v), p.IsAugmenting M := by
  sorry

/-! ## Theorem 5.2: Hall's theorem (Hall, 1935) — grade 42 -/

/-- Thm 5.2 (Hall): a bipartite `G` has a matching saturating `X` iff `|N(S)| ≥ |S|`.

## Book statement (§5.2, p. 80) — verbatim

> **Theorem 5.2** Let $G$ be a bipartite graph with bipartition $(X, Y)$. Then
> $G$ contains a matching that saturates every vertex in $X$ if and only if
> $$|N(S)| \geq |S| \quad \text{for all} \quad S \subseteq X \tag{5.2}$$

## Book proof (§5.2, pp. 80–81) — verbatim

> Suppose that $G$ contains a matching $M$ which saturates every vertex in $X$,
> and let $S$ be a subset of $X$. Since the vertices in $S$ are matched under $M$
> with distinct vertices in $N(S)$, we clearly have $|N(S)| \geq |S|$.
>
> Conversely, suppose that $G$ is a bipartite graph satisfying (5.2), but that $G$
> contains no matching saturating all the vertices in $X$. We shall obtain a
> contradiction. Let $M^*$ be a maximum matching in $G$. By our supposition,
> $M^*$ does not saturate all vertices in $X$. Let $u$ be an $M^*$-unsaturated
> vertex in $X$, and let $Z$ denote the set of all vertices connected to $u$ by
> $M^*$-alternating paths. Since $M^*$ is a maximum matching, it follows from
> theorem 5.1 that $u$ is the only $M^*$-unsaturated vertex in $Z$. Set
> $S = Z \cap X$ and $T = Z \cap Y$ (see figure 5.3).
>
> Clearly, the vertices in $S \setminus \{u\}$ are matched under $M^*$ with the
> vertices in $T$. Therefore
> $$|T| = |S| - 1 \tag{5.3}$$
> and $N(S) \supseteq T$. In fact, we have
> $$N(S) = T \tag{5.4}$$
> since every vertex in $N(S)$ is connected to $u$ by an $M^*$-alternating path.
> But (5.3) and (5.4) imply that
> $$|N(S)| = |S| - 1 < |S|$$
> contradicting assumption (5.2).

## In Lean notation

Hall's condition: no set of vertices on the `X` side may collectively have too
few neighbours.  Colloquially — no group of `k` workers may be jointly qualified
for fewer than `k` jobs.

`N(S)` is written `⋃ v ∈ S, G.neighborSet v`, and the inequality is stated as
`S.ncard ≤ (⋃ …).ncard` — the book's `|N(S)| ≥ |S|` with sides swapped.

## Proof plan

✅ **Mathlib has the combinatorial core of Hall's theorem**, so the book's proof
need not be replayed:

* `Finset.all_card_le_biUnion_card_iff_exists_injective`
  (`Combinatorics/Hall/Basic.lean`) — indexed-family form, `#s ≤ #(s.biUnion t)`
  for all `s` iff an injective transversal exists;
* `Fintype.all_card_le_rel_image_card_iff_exists_injective` — relation form,
  often the more convenient entry point here.

⚠ What Mathlib does **not** have is a bridge from either of those to
`Subgraph.IsMatching`; `Matching.lean` mentions Hall only in a doc comment.  That
bridge is the work:
1. Turn `hbip` into a family `X → Finset V` sending `x` to its neighbours.
2. Show the RHS here is that family's Hall condition — note the book's `N(S)` is
   a `Set` union while Mathlib wants a `Finset.biUnion`, so this step is a
   `Set.ncard`/`Finset.card` reconciliation.
3. Mathlib returns an injective `f : X → V`; assemble `G.Subgraph` from the edges
   `{x, f x}` and prove `IsMatching` from injectivity.

Replaying the book instead would need `berge_maximum_matching` plus an
alternating-reachability construction — much more work for the same statement.

## Status

Proved (kernel-checked, axioms `[propext, Classical.choice, Quot.sound]`).
Exactly the planned bridge: (⇐) feeds the subtype-indexed neighbourhood family
to `Finset.all_card_le_biUnion_card_iff_exists_injective` and assembles the
matching subgraph by hand from the transversal `f` (uniqueness from injectivity
of `f` plus `hbip.disjoint`); (⇒) injects `S` into `N(S)` via matching partners.
The pinned Mathlib also has this bridge as
`SimpleGraph.exists_isMatching_of_forall_ncard_le`
(`Mathlib/Combinatorics/SimpleGraph/Hall.lean`), but that file is a leaf module
not imported here; the `ncard`/`card` reconciliation step follows its script.
-/
theorem hall_bipartite_matching
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {X Y : Set V} (hbip : G.IsBipartiteWith X Y) :
    (∃ M : G.Subgraph, M.IsMatching ∧ X ⊆ M.verts) ↔
      ∀ S ⊆ X, S.ncard ≤ (⋃ v ∈ S, G.neighborSet v).ncard := (by
  classical
  constructor
  · -- (⇒): the M-partner map injects S into ⋃ v ∈ S, N(v)
    rintro ⟨M, hM, hMX⟩ S hSX
    have hpick : ∀ v ∈ S, ∃ w, M.Adj v w := fun v hv => (hM (hMX (hSX hv))).exists
    choose! g hg using hpick
    have hmem : ∀ v ∈ S, g v ∈ ⋃ u ∈ S, G.neighborSet u := fun v hv =>
      Set.mem_biUnion hv (M.adj_sub (hg v hv))
    have hinj : Set.InjOn g S := by
      intro v₁ hv₁ v₂ hv₂ heq
      have h1 : M.Adj (g v₁) v₁ := (hg v₁ hv₁).symm
      have h2 : M.Adj (g v₁) v₂ := by rw [heq]; exact (hg v₂ hv₂).symm
      exact hM.eq_of_adj_left h1 h2
    exact Set.ncard_le_ncard_of_injOn g hmem hinj (Set.toFinite _)
  · -- (⇐): Hall transversal, then hand-built matching subgraph
    intro hhall
    obtain ⟨f, hf₁, hf₂⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective
          (fun x : ↥X => G.neighborFinset ↑x)).mp
        (fun s => by
          have := hhall ↑(s.image Subtype.val) (by simp)
          rw [Set.ncard_coe_finset,
            Finset.card_image_of_injective _ Subtype.val_injective] at this
          simpa [← Set.ncard_coe_finset, neighborFinset_def])
    have hadjf : ∀ x : ↥X, G.Adj ↑x (f x) := fun x => by simpa using hf₂ x
    have hfY : ∀ x : ↥X, f x ∈ Y := fun x =>
      isBipartiteWith_neighborSet_subset hbip x.2 (by simpa using hf₂ x)
    have hfX : ∀ x : ↥X, f x ∉ X := fun x => hbip.disjoint.notMem_of_mem_right (hfY x)
    refine ⟨⟨X ∪ Set.range f,
        fun a b => (∃ x : ↥X, a = ↑x ∧ b = f x) ∨ (∃ x : ↥X, b = ↑x ∧ a = f x),
        ?_, ?_, ?_⟩, ?_, ?_⟩
    · rintro v w (⟨x, rfl, rfl⟩ | ⟨x, rfl, rfl⟩)
      · exact hadjf x
      · exact (hadjf x).symm
    · rintro v w (⟨x, rfl, -⟩ | ⟨x, -, rfl⟩)
      · exact Set.mem_union_left _ x.2
      · exact Set.mem_union_right _ (Set.mem_range_self x)
    · rintro v w (⟨x, rfl, rfl⟩ | ⟨x, rfl, rfl⟩)
      · exact Or.inr ⟨x, rfl, rfl⟩
      · exact Or.inl ⟨x, rfl, rfl⟩
    · intro v hv
      have hv' : v ∈ X ∨ v ∈ Set.range f := hv
      rcases hv' with hvX | ⟨x, rfl⟩
      · refine ⟨f ⟨v, hvX⟩, Or.inl ⟨⟨v, hvX⟩, rfl, rfl⟩, ?_⟩
        rintro w (⟨x', hvx', rfl⟩ | ⟨x', rfl, hvf'⟩)
        · exact congrArg f (Subtype.ext hvx'.symm)
        · exact absurd (hvf' ▸ hvX) (hfX x')
      · refine ⟨↑x, Or.inr ⟨x, rfl, rfl⟩, ?_⟩
        rintro w (⟨x', hfx', rfl⟩ | ⟨x', rfl, hff'⟩)
        · exact absurd (hfx'.symm ▸ x'.2) (hfX x)
        · exact congrArg Subtype.val (hf₁ hff').symm
    · exact fun v hv => Set.mem_union_left _ hv
)

/-! ## Corollary 5.2: The marriage theorem — grade 56 -/

/-- Cor 5.2: a `k`-regular bipartite graph with `k > 0` has a perfect matching.

## Book statement (§5.2, p. 81) — verbatim

> *Corollary 5.2*   If $G$ is a $k$-regular bipartite graph with $k > 0$, then
> $G$ has a perfect matching.

## Book proof (§5.2, p. 81) — verbatim

> Let $G$ be a $k$-regular bipartite graph with bipartition $(X, Y)$. Since $G$
> is $k$-regular, $k|X| = |E| = k|Y|$ and so, since $k > 0$, $|X| = |Y|$. Now let
> $S$ be a subset of $X$ and denote by $E_1$ and $E_2$ the sets of edges incident
> with vertices in $S$ and $N(S)$, respectively. By definition of $N(S)$,
> $E_1 \subseteq E_2$ and therefore
> $$k|N(S)| = |E_2| \geq |E_1| = k|S|$$
> It follows that $|N(S)| \geq |S|$ and hence, by theorem 5.2, that $G$ has a
> matching $M$ saturating every vertex in $X$. Since $|X| = |Y|$, $M$ is a perfect
> matching.

## In Lean notation

Two applications of double counting, then Hall.  The book's colourful
restatement, from which the name comes (§5.2, p. 81):

> if every girl in a village knows exactly $k$ boys, and every boy knows exactly
> $k$ girls, then each girl can marry a boy she knows, and each boy can marry a
> girl he knows.

## Proof plan

1. `|X| = |Y|`: count edges from each side.  Every edge has exactly one end in
   `X` (from `hbip`), so `|E| = ∑_{x ∈ X} d(x) = k|X|`, and symmetrically
   `k|Y|`; cancel `k` using `hk`.
2. Hall's condition: for `S ⊆ X`, the edges meeting `S` are a subset of those
   meeting `N(S)`, so `k|S| ≤ k|N(S)|`; cancel `k`.
3. `hall_bipartite_matching` gives `M` saturating `X`.
4. Upgrade to perfect: `M` saturates `X`, matches `X` injectively into `Y`, and
   `|X| = |Y|`, so it saturates `Y` too.  This step needs a counting argument —
   `IsMatching` plus `X ⊆ M.verts` does not immediately give `M.IsSpanning`.

## Status

Proved (kernel-checked, axioms `[propext, Classical.choice, Quot.sound]`), by a
shorter route than the plan above: one double count
(`Finset.card_nsmul_le_card_nsmul` shows k-regularity gives the *global* Hall
condition `∀ s : Set V, s.ncard ≤ N(s).ncard` — each vertex of `s` sends `k`
edge-ends into `N(s)`, each vertex of `N(s)` absorbs at most `k`), then direct
reuse of Mathlib's `exists_isPerfectMatching_of_forall_ncard_le`
(`Mathlib/Combinatorics/SimpleGraph/Hall.lean`), which subsumes steps 1, 3 and 4
— including the saturation→spanning upgrade flagged above.  Neither
bipartiteness side of the plan's `|X| = |Y|` count is needed explicitly.
-/
theorem marriage_theorem
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {X Y : Set V} (hbip : G.IsBipartiteWith X Y)
    {k : ℕ} (hk : 0 < k) (hreg : G.IsRegularOfDegree k) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := (by
  classical
  have hglobal : ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
    intro s
    have hsfin : s.Finite := Set.toFinite s
    have hNfin : (⋃ x ∈ s, G.neighborSet x).Finite := Set.toFinite _
    have hmain : hsfin.toFinset.card • k ≤ hNfin.toFinset.card • k := by
      refine Finset.card_nsmul_le_card_nsmul G.Adj (fun a ha => ?_) (fun b hb => ?_)
      · have hsub : G.neighborFinset a ⊆ hNfin.toFinset.bipartiteAbove G.Adj a := by
          intro b hb
          rw [SimpleGraph.mem_neighborFinset] at hb
          rw [Finset.mem_bipartiteAbove]
          exact ⟨hNfin.mem_toFinset.mpr (Set.mem_biUnion (hsfin.mem_toFinset.mp ha) hb), hb⟩
        have hcard := Finset.card_le_card hsub
        rwa [SimpleGraph.card_neighborFinset_eq_degree, hreg a] at hcard
      · have hsub : hsfin.toFinset.bipartiteBelow G.Adj b ⊆ G.neighborFinset b := by
          intro a ha
          rw [Finset.mem_bipartiteBelow] at ha
          rw [SimpleGraph.mem_neighborFinset]
          exact ha.2.symm
        have hcard := Finset.card_le_card hsub
        rwa [SimpleGraph.card_neighborFinset_eq_degree, hreg b] at hcard
    have hmul : hsfin.toFinset.card * k ≤ hNfin.toFinset.card * k := by
      simpa only [smul_eq_mul, nsmul_eq_mul] using hmain
    rw [Set.ncard_eq_toFinset_card s hsfin, Set.ncard_eq_toFinset_card _ hNfin]
    exact Nat.le_of_mul_le_mul_right hmul hk
  exact SimpleGraph.exists_isPerfectMatching_of_forall_ncard_le hbip hglobal
)

/-! ## (5.5): Every matching is at most every covering — grade 47, build first -/

/-- (5.5): for any matching `M` and covering `K`, `|M| ≤ |K|`.

## Book statement (§5.2, p. 82) — verbatim

> If $K$ is a covering of $G$, and $M$ is a matching of $G$, then $K$ contains at
> least one end of each of the edges in $M$. Thus, for any matching $M$ and any
> covering $K$, $|M| \le |K|$. Indeed, if $M^*$ is a maximum matching and
> $\tilde{K}$ is a minimum covering, then
> $$|M^*| \le |\tilde{K}| \tag{5.5}$$

The book states this inline, without a theorem number or separate proof.

## In Lean notation

The edges of a matching are pairwise disjoint and the covering must contain an
endpoint of each; since no two matching edges share an endpoint, the chosen
endpoints are distinct, so `K` has at least `|M|` elements.

The book continues:

> In general, equality does not hold in (5.5) (see, for example, figure 5.4).
> However, if $G$ is bipartite we do have $|M^*| = |\tilde{K}|$.

which is König's Theorem 5.3.

## Proof plan

Injection from `M.edgeSet` into `K`:
1. For each `e ∈ M.edgeSet`, `hK` picks an endpoint lying in `K`.  ⚠ This is a
   *choice* over `Sym2`, so use `Sym2.ind` plus `Classical.choice`, or define the
   map on representatives and show it respects `Sym2` equality.
2. Injectivity: two distinct matching edges sharing the chosen endpoint would
   contradict `hM.IsMatching` (a matching vertex has a unique incident edge).
3. `Set.ncard_le_ncard_of_injOn` finishes.

## Status

`sorry`.  The mathematics is trivial; the friction is entirely in the `Sym2`
endpoint choice at step 1.  Worth doing early — Lemma 5.3 and König both depend
on it, and the file header marks it "build first".
-/
theorem matching_card_le_covering_card
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMatching) {K : Set V} (hK : G.IsCovering K) :
    M.edgeSet.ncard ≤ K.ncard := (by
  classical
  rcases Set.eq_empty_or_nonempty M.edgeSet with hME | ⟨e₀, -⟩
  · simp [hME]
  · haveI : Nonempty V := ⟨e₀.out.1⟩
    have hpick : ∀ e ∈ M.edgeSet, ∃ x, x ∈ K ∧ x ∈ e :=
      Sym2.ind (f := fun e => e ∈ M.edgeSet → ∃ x, x ∈ K ∧ x ∈ e) fun u v he => by
        have hadj : M.Adj u v := Subgraph.mem_edgeSet.mp he
        rcases hK (M.adj_sub hadj) with hu | hv
        · exact ⟨u, hu, Sym2.mem_mk_left u v⟩
        · exact ⟨v, hv, Sym2.mem_mk_right u v⟩
    choose! f hfK hfe using hpick
    have hinj : Set.InjOn f M.edgeSet := by
      intro e₁ he₁ e₂ he₂ hfeq
      have hx₁ : f e₁ ∈ e₁ := hfe e₁ he₁
      have hx₂ : f e₁ ∈ e₂ := by rw [hfeq]; exact hfe e₂ he₂
      have hs₁ : s(f e₁, Sym2.Mem.other hx₁) = e₁ := Sym2.other_spec hx₁
      have hs₂ : s(f e₁, Sym2.Mem.other hx₂) = e₂ := Sym2.other_spec hx₂
      have hadj₁ : M.Adj (f e₁) (Sym2.Mem.other hx₁) := by
        rw [← Subgraph.mem_edgeSet, hs₁]; exact he₁
      have hadj₂ : M.Adj (f e₁) (Sym2.Mem.other hx₂) := by
        rw [← Subgraph.mem_edgeSet, hs₂]; exact he₂
      have hy : Sym2.Mem.other hx₁ = Sym2.Mem.other hx₂ := hM.eq_of_adj_left hadj₁ hadj₂
      rw [← hs₁, ← hs₂, hy]
    exact Set.ncard_le_ncard_of_injOn f hfK hinj (Set.toFinite K)
)

/-! ## Lemma 5.3: Matching/covering of equal size are both extremal — grade 51 -/

/-- Lem 5.3: if `|M| = |K|` then `M` is a maximum matching and `K` a minimum covering.

## Book statement (§5.2, p. 82) — verbatim

> **Lemma 5.3** Let $M$ be a matching and $K$ be a covering such that
> $|M| = |K|$. Then $M$ is a maximum matching and $K$ is a minimum covering.

## Book proof (§5.2, p. 82) — verbatim

> If $M^*$ is a maximum matching and $\tilde{K}$ is a minimum covering then, by
> (5.5),
> $$|M| \le |M^*| \le |\tilde{K}| \le |K|$$
> Since $|M| = |K|$, it follows that $|M| = |M^*|$ and $|K| = |\tilde{K}|$.

## In Lean notation

The standard "weak duality certifies optimality" argument: exhibiting a matching
and a covering of the same size proves both optimal at once.  It is exactly how
Theorem 5.3 is proved.

## Proof plan

1. ⚠ The book's chain needs a maximum matching `M*` and a minimum covering `K̃`
   to *exist*.  Neither is given as a hypothesis here, so both must be produced —
   by finiteness of `V`, extremal elements exist (`Set.Finite.exists_maximal_wrt`
   over matching sizes, similarly for coverings).  This is the only step with any
   content.
2. Chain `|M| ≤ |M*| ≤ |K̃| ≤ |K|` using `matching_card_le_covering_card` for the
   middle and extremality for the ends.
3. `hcard` collapses the chain; read off both conclusions.

## Status

`sorry`, and depends on `matching_card_le_covering_card`.
-/
theorem isMaximumMatching_and_isMinimumCovering_of_card_eq
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMatching) {K : Set V} (hK : G.IsCovering K)
    (hcard : M.edgeSet.ncard = K.ncard) :
    M.IsMaximumMatching ∧ G.IsMinimumCovering K := (by
  refine ⟨⟨hM, fun M' hM' => ?_⟩, ⟨hK, fun K' hK' => ?_⟩⟩
  · calc M'.edgeSet.ncard ≤ K.ncard := matching_card_le_covering_card hM' hK
      _ = M.edgeSet.ncard := hcard.symm
  · calc K.ncard = M.edgeSet.ncard := hcard.symm
      _ ≤ K'.ncard := matching_card_le_covering_card hM hK'
)

/-! ## Theorem 5.3: König's theorem (König, 1931) — grade 82 -/

/-- Thm 5.3 (König): in a bipartite graph, max-matching size = min-covering size.

## Book statement (§5.2, p. 82) — verbatim

> **Theorem 5.3** In a bipartite graph, the number of edges in a maximum matching
> is equal to the number of vertices in a minimum covering.

## Book proof (§5.2, pp. 82–83) — verbatim

> Let $G$ be a bipartite graph with bipartition $(X, Y)$, and let $M^*$ be a
> maximum matching of $G$. Denote by $U$ the set of $M^*$-unsaturated vertices in
> $X$, and by $Z$ the set of all vertices connected by $M^*$-alternating paths to
> vertices of $U$. Set $S = Z \cap X$ and $T = Z \cap Y$. Then, as in the proof of
> theorem 5.2, we have that every vertex in $T$ is $M^*$-saturated and
> $N(S) = T$. Define $\tilde{K} = (X \backslash S) \cup T$ (see figure 5.5). Every
> edge of $G$ must have at least one of its ends in $\tilde{K}$. For, otherwise,
> there would be an edge with one end in $S$ and one end in $Y\backslash T$,
> contradicting $N(S) = T$. Thus $\tilde{K}$ is a covering of $G$ and clearly
> $$|M^*| = |\tilde{K}|$$
> By lemma 5.3, $\tilde{K}$ is a minimum covering, and the theorem follows.

## In Lean notation

The prototypical min-max theorem of combinatorics — maximum packing equals
minimum cover.  Closely related to Hall's theorem: exercise 5.2.7 asks to derive
Hall from König, and its matrix form is exercise 5.2.5.

Note the Lean statement takes *both* extremal objects as hypotheses (`hM`, `hK`)
and concludes their sizes agree, rather than constructing `K̃` as the book does.

## Proof plan

1. Build the book's `K̃ = (X \ S) ∪ T` from `M`:
   * `U` = `M`-unsaturated vertices of `X`;
   * `Z` = vertices reachable from `U` by `M`-alternating paths;
   * `S = Z ∩ X`, `T = Z ∩ Y`.
2. `N(S) = T` — the same alternating-reachability fact Hall's proof needs.  ⚠
   Since `hall_bipartite_matching` is planned to go via Mathlib rather than the
   book's argument, this fact is **not** available as a by-product and must be
   proved here directly.
3. `K̃` is a covering: an edge escaping it would run `S → Y \ T`, contradicting
   step 2.
4. `|M| = |K̃|` by counting: each `M`-edge contributes exactly one end to `K̃`.
5. `isMaximumMatching_and_isMinimumCovering_of_card_eq` makes `K̃` minimum, and
   `hK` then forces `|K| = |K̃| = |M|`.

## Status

Proved (kernel-checked, axioms `[propext, Classical.choice, Quot.sound]`) — and
contrary to the warning above, the alternating-path machinery *was* avoided.
The landed proof uses a different route than the book: `≤` is weak duality
(`matching_card_le_covering_card`); for `≥`, minimality of `K` first forces
every `K`-vertex to meet an edge (so `K ⊆ X ∪ Y`), then an `aux` block applies
the in-file `hall_bipartite_matching` once per side of the cover to an
auxiliary crossing graph (`K ∩ W` vs `Z \ K`), where Hall's condition holds
because a deficient `S` would yield the strictly smaller covering
`(K \ S) ∪ N(S)` — minimality of `K` again.  The two matchings have supports in
disjoint vertex sets, so their `⊔` is a matching (`IsMatching.sup`) saturating
`K` with no edge inside `K`, and `v ↦ s(v, partner v)` injects `K` into its
edge set; maximality of `M` finishes.
-/
theorem konig_matching_covering
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {X Y : Set V} (hbip : G.IsBipartiteWith X Y)
    {M : G.Subgraph} (hM : M.IsMaximumMatching)
    {K : Set V} (hK : G.IsMinimumCovering K) :
    M.edgeSet.ncard = K.ncard := (by
  classical
  refine le_antisymm (matching_card_le_covering_card hM.1 hK.1) ?_
  rcases Set.eq_empty_or_nonempty K with hKe | ⟨v₀, hv₀⟩
  · simp [hKe]
  · haveI : Nonempty V := ⟨v₀⟩
    -- Step 1: every vertex of the minimum covering K meets an edge of G
    have hKedge : ∀ v ∈ K, ∃ w, G.Adj v w := by
      intro v hv
      by_contra hno
      push_neg at hno
      have hcov : G.IsCovering (K \ {v}) := by
        intro a b hab
        rcases hK.1 hab with h | h
        · exact Or.inl (Set.mem_diff_singleton.mpr ⟨h, fun hav => hno b (hav ▸ hab)⟩)
        · exact Or.inr (Set.mem_diff_singleton.mpr ⟨h, fun hbv => hno a (hbv ▸ hab.symm)⟩)
      have h1 := hK.2 _ hcov
      have h2 := Set.ncard_diff_singleton_lt_of_mem hv (Set.toFinite K)
      omega
    -- Step 2: K lies in X ∪ Y
    have hKXY : ∀ v ∈ K, v ∈ X ∨ v ∈ Y := by
      intro v hv
      obtain ⟨w, hw⟩ := hKedge v hv
      rcases hbip.mem_of_adj hw with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    -- Steps 3–6 (one Hall application per side, done symmetrically):
    -- a matching saturating K ∩ W whose edges all cross from K ∩ W to Z \ K
    have aux : ∀ W Z : Set V, G.IsBipartiteWith W Z →
        ∃ N : G.Subgraph, N.IsMatching ∧ K ∩ W ⊆ N.verts ∧
          ∀ ⦃a b : V⦄, N.Adj a b → a ∈ K ∩ W ∧ b ∈ Z \ K ∨ b ∈ K ∩ W ∧ a ∈ Z \ K := by
      intro W Z hWZ
      let G₁ : SimpleGraph V :=
        { Adj := fun a b =>
            G.Adj a b ∧ a ∈ K ∩ W ∧ b ∈ Z \ K ∨ G.Adj b a ∧ b ∈ K ∩ W ∧ a ∈ Z \ K
          symm := fun a b h => h.symm
          loopless := fun a h => by
            rcases h with ⟨hh, -⟩ | ⟨hh, -⟩ <;> exact G.loopless a hh }
      have hG₁adj : ∀ a b : V, G₁.Adj a b ↔
          (G.Adj a b ∧ a ∈ K ∩ W ∧ b ∈ Z \ K ∨ G.Adj b a ∧ b ∈ K ∩ W ∧ a ∈ Z \ K) :=
        fun a b => Iff.rfl
      haveI : DecidableRel G₁.Adj := fun a b => Classical.propDecidable _
      have hbip₁ : G₁.IsBipartiteWith (K ∩ W) (Z \ K) := by
        refine ⟨Set.disjoint_left.mpr fun a ha hb => hb.2 ha.1, ?_⟩
        intro a b hab
        rcases (hG₁adj a b).mp hab with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h2, h1⟩
      -- Step 4: the Hall condition, by minimality of K
      have hall₁ : ∀ S ⊆ K ∩ W, S.ncard ≤ (⋃ v ∈ S, G₁.neighborSet v).ncard := by
        intro S hS
        by_contra hlt
        push_neg at hlt
        have hSK : S ⊆ K := fun v hv => (hS hv).1
        have key : ∀ u v : V, G.Adj u v → u ∈ K →
            u ∈ (K \ S) ∪ (⋃ x ∈ S, G₁.neighborSet x) ∨
              v ∈ (K \ S) ∪ (⋃ x ∈ S, G₁.neighborSet x) := by
          intro u v huv huK
          by_cases huS : u ∈ S
          · have hvZ : v ∈ Z := hWZ.mem_of_mem_adj (hS huS).2 huv
            by_cases hvK : v ∈ K
            · refine Or.inr (Set.mem_union_left _ ⟨hvK, fun hvS => ?_⟩)
              exact Set.disjoint_left.mp hWZ.disjoint (hS hvS).2 hvZ
            · refine Or.inr (Set.mem_union_right _ (Set.mem_biUnion huS ?_))
              exact (G₁.mem_neighborSet u v).mpr
                ((hG₁adj u v).mpr (Or.inl ⟨huv, hS huS, hvZ, hvK⟩))
          · exact Or.inl (Set.mem_union_left _ ⟨huK, huS⟩)
        have hcov : G.IsCovering ((K \ S) ∪ (⋃ x ∈ S, G₁.neighborSet x)) := by
          intro a b hab
          rcases hK.1 hab with h | h
          · exact key a b hab h
          · exact (key b a hab.symm h).symm
        have h1 := hK.2 _ hcov
        have h2 := Set.ncard_union_le (K \ S) (⋃ x ∈ S, G₁.neighborSet x)
        have h3 := Set.ncard_diff_add_ncard_of_subset hSK (Set.toFinite K)
        omega
      obtain ⟨M₁, hM₁m, hM₁v⟩ := (hall_bipartite_matching G₁ hbip₁).mpr hall₁
      have hsub : ∀ ⦃a b : V⦄, M₁.Adj a b → G.Adj a b := by
        intro a b hab
        rcases (hG₁adj a b).mp (M₁.adj_sub hab) with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact h.symm
      refine ⟨⟨M₁.verts, M₁.Adj, fun hab => hsub hab, M₁.edge_vert, M₁.symm⟩, ?_, ?_, ?_⟩
      · intro v hv
        exact hM₁m hv
      · exact hM₁v
      · intro a b hab
        rcases (hG₁adj a b).mp (M₁.adj_sub hab) with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
    obtain ⟨N₁, hN₁m, hN₁v, hN₁adj⟩ := aux X Y hbip
    obtain ⟨N₂, hN₂m, hN₂v, hN₂adj⟩ := aux Y X hbip.symm
    -- Step 6: the two matchings live on disjoint vertex sets, so their sup is a matching
    have hN₁verts : N₁.verts ⊆ (K ∩ X) ∪ (Y \ K) := by
      intro v hv
      obtain ⟨w, hw, -⟩ := hN₁m hv
      rcases hN₁adj hw with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact Set.mem_union_left _ h1
      · exact Set.mem_union_right _ h2
    have hN₂verts : N₂.verts ⊆ (K ∩ Y) ∪ (X \ K) := by
      intro v hv
      obtain ⟨w, hw, -⟩ := hN₂m hv
      rcases hN₂adj hw with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact Set.mem_union_left _ h1
      · exact Set.mem_union_right _ h2
    have hdisj : Disjoint N₁.support N₂.support := by
      have hbig : Disjoint ((K ∩ X) ∪ (Y \ K)) ((K ∩ Y) ∪ (X \ K)) := by
        rw [Set.disjoint_left]
        intro a ha hb
        simp only [Set.mem_union] at ha hb
        rcases ha with h1 | h1 <;> rcases hb with h2 | h2
        · exact Set.disjoint_left.mp hbip.disjoint h1.2 h2.2
        · exact h2.2 h1.1
        · exact h1.2 h2.1
        · exact Set.disjoint_left.mp hbip.disjoint h2.1 h1.1
      exact hbig.mono (N₁.support_subset_verts.trans hN₁verts)
        (N₂.support_subset_verts.trans hN₂verts)
    have hM₀ : (N₁ ⊔ N₂).IsMatching := hN₁m.sup hN₂m hdisj
    have hKsub : K ⊆ (N₁ ⊔ N₂).verts := by
      intro v hv
      rw [Subgraph.verts_sup]
      rcases hKXY v hv with hX | hY
      · exact Set.mem_union_left _ (hN₁v ⟨hv, hX⟩)
      · exact Set.mem_union_right _ (hN₂v ⟨hv, hY⟩)
    -- Step 7: no edge of N₁ ⊔ N₂ has both ends in K, so partners inject K into the edges
    have hedgeK : ∀ a b : V, (N₁ ⊔ N₂).Adj a b → a ∈ K → b ∈ K → False := by
      intro a b hab haK hbK
      rcases Subgraph.sup_adj.mp hab with h | h
      · rcases hN₁adj h with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact h2.2 hbK
        · exact h2.2 haK
      · rcases hN₂adj h with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact h2.2 hbK
        · exact h2.2 haK
    have hpick : ∀ v ∈ K, ∃ w, (N₁ ⊔ N₂).Adj v w := fun v hv => (hM₀ (hKsub hv)).exists
    choose! p hp using hpick
    have hinj : Set.InjOn (fun v => s(v, p v)) K := by
      intro v₁ h₁ v₂ h₂ he
      have he' : s(v₁, p v₁) = s(v₂, p v₂) := he
      rcases Sym2.eq_iff.mp he' with ⟨h, -⟩ | ⟨ha, -⟩
      · exact h
      · exfalso
        have hadj : (N₁ ⊔ N₂).Adj v₂ v₁ := by rw [ha]; exact hp v₂ h₂
        exact hedgeK v₂ v₁ hadj h₂ h₁
    have hle1 : K.ncard ≤ (N₁ ⊔ N₂).edgeSet.ncard :=
      Set.ncard_le_ncard_of_injOn (fun v => s(v, p v))
        (fun v hv => Subgraph.mem_edgeSet.mpr (hp v hv)) hinj (Set.toFinite _)
    exact hle1.trans (hM.2 _ hM₀)
)

/-! ## Theorem 5.4: Tutte's theorem (Tutte, 1947) — WRAPPER over `SimpleGraph.tutte`, grade 7 -/

/-- Thm 5.4 (Tutte): `G` has a perfect matching iff `o(G − S) ≤ |S|` for all `S`.

## Book statement (§5.3, p. 84) — verbatim

> *Theorem 5.4* $G$ has a perfect matching if and only if
> $$o(G - S) \leq |S| \quad \text{for all} \quad S \subset V \tag{5.6}$$

with, from the same page:

> A component of a graph is *odd* or *even* according as it has an odd or even
> number of vertices. We denote by $o(G)$ the number of odd components of $G$.

## Book proof (§5.3, pp. 84–87) — outline

The (⇒) direction is short:

> Suppose first that $G$ has a perfect matching $M$. Let $S$ be a proper subset
> of $V$, and let $G_1, G_2, \ldots, G_n$ be the odd components of $G - S$.
> Because $G_i$ is odd, some vertex $u_i$ of $G_i$ must be matched under $M$ with
> a vertex $v_i$ of $S$ (see figure 5.6). Therefore, since
> $\{v_1, v_2, \ldots, v_n\} \subseteq S$
> $$o(G - S) = n = |\{v_1, v_2, \ldots, v_n\}| \leq |S|$$

The converse is Lovász's argument: embed `G` in a *maximal* graph `G*` with no
perfect matching; show `G* - U` is a disjoint union of complete graphs, where
`U` is the set of vertices of degree `ν - 1`; then match one vertex of each odd
component into `U` and pair the rest.  The structure step is proved by taking
perfect matchings `M₁` of `G* + xz` and `M₂` of `G* + yw` and analysing the even
cycles of `M₁ Δ M₂` in two cases.  (Full text, pp. 85–87.)

## In Lean notation

The obstruction to a perfect matching is a set `S` whose removal leaves more odd
pieces than `S` has vertices — each odd piece must "export" a vertex to be
matched into `S`.

## Proof plan

✅ **This is a one-liner.**  Mathlib proves Tutte's theorem as
`SimpleGraph.tutte` (`Combinatorics/SimpleGraph/Tutte.lean`):

    theorem tutte : (∃ M : Subgraph G, M.IsPerfectMatching) ↔ ∀ u, ¬ G.IsTutteViolator u

where `IsTutteViolator G u := u.ncard < ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents.ncard`.

So `¬ IsTutteViolator u` unfolds to `¬ (u.ncard < …)`, which is `not_lt` away
from the `… ≤ u.ncard` stated here — and the `deleteVerts`/`oddComponents`
spelling already matches this file's exactly.  The proof should be

    G.tutte.trans (by simp [IsTutteViolator, not_lt])

or close to it.

Note the book quantifies over *proper* subsets `S ⊂ V` while both Mathlib and
this file quantify over all `S`; at `S = V` the induced graph is empty, so the
extra case is harmless.

## Status

`sorry`, but should be the cheapest theorem in the file to close.
-/
theorem tutte_perfect_matching {V : Type*} [Finite V] (G : SimpleGraph V) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∀ S : Set V, ((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard ≤ S.ncard := (by
  rw [SimpleGraph.tutte]
  constructor
  · intro h S
    exact not_lt.mp (h S)
  · intro h u
    exact not_lt.mpr (h u)
)

/-! ## Corollary 5.4: Petersen's theorem (Petersen, 1891) — grade 58 -/

/-- Cor 5.4 (Petersen, 1891): every 3-regular graph without cut edges has a
perfect matching.

## Book statement (§5.3, p. 87) — verbatim

> *Corollary 5.4* Every 3-regular graph without cut edges has a perfect matching.

## Book proof (§5.3, p. 87) — verbatim

> Let $G$ be a 3-regular graph without cut edges, and let $S$ be a proper subset
> of $V$. Denote by $G_1, G_2, \ldots, G_n$ the odd components of $G - S$, and let
> $m_i$ be the number of edges with one end in $G_i$ and one end in $S$,
> $1 \leq i \leq n$. Since $G$ is 3-regular
> $$\sum_{v \in V(G_i)} d(v) = 3\nu(G_i) \quad \text{for} \quad 1 \leq i \leq n \tag{5.8}$$
> and
> $$\sum_{v \in S} d(v) = 3 |S| \tag{5.9}$$
> By (5.8), $m_i = \sum_{v \in V(G_i)} d(v) - 2\varepsilon(G_i)$ is odd. Now
> $m_i \neq 1$ since $G$ has no cut edge. Thus
> $$m_i \geq 3 \quad \text{for} \quad 1 \leq i \leq n \tag{5.10}$$
> It follows from (5.10) and (5.9) that
> $$o(G - S) = n \leq \frac{1}{3} \sum_{i=1}^{n} m_i \leq \frac{1}{3} \sum_{v \in S} d(v) = |S|$$
> Therefore, by theorem 5.4, $G$ has a perfect matching.

## In Lean notation

A double count per odd component, then Tutte.  The parity step is the crux:
`mᵢ = 3ν(Gᵢ) - 2ε(Gᵢ)` is odd because `ν(Gᵢ)` is odd, and bridgelessness then
upgrades `mᵢ ≥ 1` to `mᵢ ≥ 3`.

⚠ The book's `⅓ ∑ mᵢ ≤ ⅓ ∑_{v ∈ S} d(v)` is over `ℚ`.  In `ℕ` this should be
cleared to `3n ≤ ∑ mᵢ ≤ 3|S|` and divided only at the end, or done in `ℤ`.

## Proof plan

1. Apply `tutte_perfect_matching` (⇐); fix `S` and bound `o(G - S)`.
2. For each odd component, define `mᵢ` as the size of the edge boundary.
3. Parity: `mᵢ` odd, via handshaking inside the component.
4. `mᵢ ≠ 1`: a single boundary edge would be a bridge, contradicting `hbridge`.
   ⚠ This needs "edge boundary of size 1 implies `IsBridge`", which is not in the
   file and not in Mathlib in this form.
5. Sum: `3n ≤ ∑ mᵢ ≤ ∑_{v ∈ S} d(v) = 3|S|`, so `n ≤ |S|`.

## Book remark (§5.3, p. 87) — verbatim

> A 3-regular graph with cut edges need not have a perfect matching. For example,
> it follows from theorem 5.4 that the graph $G$ of figure 5.10 has no perfect
> matching, since $o(G - v) = 3$.

## Status

`sorry`.  Depends on `tutte_perfect_matching` (cheap, see there) plus the
component-boundary bookkeeping of steps 2–4, which is the actual work.
-/
theorem petersen_three_regular_bridgeless
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3) (hbridge : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  sorry

/-! ## Theorem 5.5: Equality subgraph ⇒ optimal matching (Kuhn 1955 / Munkres 1957) — grade 65

NOTE: the outline recommends representing weights as `w : Sym2 V → ℝ` (rather than
`V → V → ℝ`), which discharges `equalitySubgraph`'s `symm` obligation definitionally.
We adopt that representation here. -/

/-- Feasible vertex labelling: `l x + l y ≥ w s(x,y)`. ⚠ MISSING. Honest def.

## Book definition (§5.5, p. 94) — verbatim

> We define a *feasible vertex labelling* as a real-valued function $l$ on the
> vertex set $X \cup Y$ such that, for all $x \in X$ and $y \in Y$
> $$l(x) + l(y) \geq w(xy) \tag{5.11}$$
> (The real number $l(v)$ is called the *label* of the vertex $v$.) [...] No
> matter what the edge weights are, there always exists a feasible vertex
> labelling; one such is the function $l$ given by
> $$l(x) = \max_{y \in Y} w(xy) \ \text{if} \ x \in X, \qquad l(y) = 0 \ \text{if} \ y \in Y \tag{5.12}$$

## In Lean notation

Assign a label to every vertex so the two labels at an edge's ends sum to at
least its weight.  Weights are carried as `w : Sym2 V → ℝ` rather than
`V → V → ℝ`, which makes symmetry automatic.

Labels are the dual objects to matchings: `∑_v l(v)` upper-bounds the weight of
any perfect matching, and Theorem 5.5 says a matching attaining that bound is
optimal.

⚠ The existence claim (5.12) is **not** stated as a lemma anywhere in this file,
though the Kuhn–Munkres algorithm needs it as its starting point.
-/
def IsFeasibleLabelling {V : Type*} (w : Sym2 V → ℝ) (X Y : Set V) (l : V → ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, w s(x, y) ≤ l x + l y

/-- The **equality subgraph** `G_l`. ⚠ MISSING. Honest def.

## Book definition (§5.5, p. 94) — verbatim

> If $l$ is a feasible vertex labelling, we denote by $E_l$ the set of those edges
> for which equality holds in (5.11); that is
> $$E_l = \{xy \in E \mid l(x) + l(y) = w(xy)\}$$
> The spanning subgraph of $G$ with edge set $E_l$ is referred to as the *equality
> subgraph* corresponding to the feasible vertex labelling $l$, and is denoted by
> $G_l$.

## In Lean notation

Keep only the edges that are "tight" for the labelling — those whose weight
exactly uses up the sum of the labels at their ends.  As the Kuhn–Munkres
algorithm adjusts labels the equality subgraph changes, and the algorithm stops
once some equality subgraph contains a perfect matching.

Representing weights as `Sym2 V → ℝ` makes `l x + l y = w s(x,y)` symmetric in
`x, y` definitionally, which is why the `symm` obligation is routine.

## Status

Fully defined — `symm` and `loopless` were proved this session (previously `sorry`
proof fields).
-/
def equalitySubgraph {V : Type*} (w : Sym2 V → ℝ) (G : SimpleGraph V) (l : V → ℝ) :
    SimpleGraph V where
  Adj x y := G.Adj x y ∧ l x + l y = w s(x, y)
  symm := by
    rintro x y ⟨hadj, heq⟩
    exact ⟨hadj.symm, by rw [add_comm, Sym2.eq_swap]; exact heq⟩
  loopless := fun x h => G.loopless x h.1

/-- Weight of a matching.

## Book definition (§5.5, p. 94)

The book uses the notation `w(M)` without a display, in (5.13)–(5.14):

> $$w(M^*) = \sum_{e \in M^*} w(e) = \sum_{v \in V} l(v) \tag{5.13}$$

## In Lean notation

`∑ᶠ e ∈ M.edgeSet, w e`, using the *finsum* `∑ᶠ` rather than `Finset.sum` so that
no `Fintype (M.edgeSet)` instance has to be threaded through — `M.edgeSet` is a
`Set`, and finsum handles the finiteness side condition implicitly.

## Reading

In the personnel-assignment setting `w(xᵢyⱼ)` is the effectiveness of worker `Xᵢ`
in job `Yⱼ`, and `w(M)` the total effectiveness of assignment `M`.
-/
noncomputable def matchingWeight {V : Type*} (w : Sym2 V → ℝ) {G : SimpleGraph V}
    (M : G.Subgraph) : ℝ :=
  ∑ᶠ e ∈ M.edgeSet, w e

/-- An **optimal matching**: a max-weight perfect matching. ⚠ MISSING. Honest def.

## Book definition (§5.5, p. 94) — verbatim

> The optimal assignment problem is clearly equivalent to that of finding a
> maximum-weight perfect matching in this weighted graph. We shall refer to such
> a matching as an *optimal matching.*

## In Lean notation

Among all assignments of each worker to a distinct job, the one of greatest total
effectiveness.  Maximality is spelled out by hand, as with
`Subgraph.IsMaximumMatching`.

## Context (§5.5, p. 94) — verbatim

> To solve the optimal assignment problem it is, of course, possible to enumerate
> all $n!$ perfect matchings and find an optimal one among them. However, for
> large $n$, such a procedure would clearly be most inefficient.

The Kuhn–Munkres algorithm, founded on Theorem 5.5 below, does it efficiently.
The algorithm itself is not formalised in this file — only the theorem that
justifies its stopping condition.
-/
def IsOptimalMatching {V : Type*} (w : Sym2 V → ℝ) (G : SimpleGraph V) (M : G.Subgraph) : Prop :=
  M.IsPerfectMatching ∧
    ∀ M' : G.Subgraph, M'.IsPerfectMatching → matchingWeight w M' ≤ matchingWeight w M

/-- Thm 5.5: a perfect matching in the equality subgraph is an optimal matching of `G`.

## Book statement (§5.5, p. 94) — verbatim

> *Theorem 5.5* Let $l$ be a feasible vertex labelling of $G$. If $G_l$ contains
> a perfect matching $M^*$, then $M^*$ is an optimal matching of $G$.

## Book proof (§5.5, p. 95) — verbatim

> Suppose that $G_l$ contains a perfect matching $M^*$. Since $G_l$ is a spanning
> subgraph of $G$, $M^*$ is also a perfect matching of $G$. Now
> $$w(M^*) = \sum_{e \in M^*} w(e) = \sum_{v \in V} l(v) \tag{5.13}$$
> since each $e \in M^*$ belongs to the equality subgraph and the ends of edges of
> $M^*$ cover each vertex exactly once. On the other hand, if $M$ is any perfect
> matching of $G$, then
> $$w(M) = \sum_{e \in M} w(e) \le \sum_{v \in V} l(v) \tag{5.14}$$
> It follows from (5.13) and (5.14) that $w(M^*) \ge w(M)$. Thus $M^*$ is an
> optimal matching.

## In Lean notation

Weak duality certifying optimality again: `∑_v l(v)` bounds every perfect
matching from above, and one attaining the bound must be best.  This is the
foundation of the Kuhn–Munkres algorithm, which alternates the Hungarian method
inside `G_l` with label adjustments that grow `G_l`.

The conclusion transports `M` along `Hom.ofLE` from `equalitySubgraph w G l` up
to `G`, since the two live over different graphs.

## Proof plan

1. ⚠ Discharge the inline `sorry` in the statement itself:
   `equalitySubgraph w G l ≤ G` is immediate from the first conjunct of its
   `Adj`.  This is a genuine `sorry` *inside the theorem's type*, so it must be
   fixed before the statement means what it should.
2. `M.map …` is a perfect matching of `G` — `Hom.ofLE` is injective on vertices,
   so spanning and matching both transport.
3. (5.13): each edge of `M` is tight, so `w e = l x + l y`; summing over a
   perfect matching counts each vertex once, giving `∑ᶠ = ∑ v, l v`.  Needs a
   "perfect matching edge-sum equals vertex-sum" lemma — the main work.
4. (5.14): for arbitrary perfect `M'`, feasibility gives `w e ≤ l x + l y`
   edgewise; sum and reuse step 3's counting.
5. Combine.

⚠ Steps 3–4 both need `hcov : X ∪ Y = Set.univ` to know the vertex sum ranges
over everything, and step 4 needs `hbip` to place each edge's ends in `X` and `Y`
respectively before `hl` applies.

## Status

`sorry`.  ✅ The former second `sorry` *inside the statement's type* (the
`Hom.ofLE` obligation) was replaced with the real proof `fun _ _ h => h.1` this
session, so the statement itself is now `sorryAx`-free and means what it says.
-/
theorem optimal_of_perfectMatching_equalitySubgraph
    {V : Type*} [Fintype V] [DecidableEq V] (w : Sym2 V → ℝ) (G : SimpleGraph V)
    {X Y : Set V} (hbip : G.IsBipartiteWith X Y) (hcov : X ∪ Y = Set.univ)
    (l : V → ℝ) (hl : IsFeasibleLabelling w X Y l)
    {M : (equalitySubgraph w G l).Subgraph} (hM : M.IsPerfectMatching) :
    IsOptimalMatching w G
      (M.map (Hom.ofLE (fun _ _ h => h.1 : equalitySubgraph w G l ≤ G))) := by
  sorry

/-! ## Key Exercises -/

/-- Ex 5.1.1(a): every `k`-cube (`k ≥ 2`) has a perfect matching.

## Book statement (§5.1, p. 79) — verbatim

> **5.1.1** (a) Show that every $k$-cube has a perfect matching $(k \geq 2)$.

An exercise, so the book gives no proof.

## In Lean notation

The `k`-cube is `k`-regular and bipartite (sides given by the parity of the
number of `1`s), so for `k ≥ 2` Corollary 5.2 applies.

## Proof plan

✅ **Do not route through Corollary 5.2** — an explicit matching is far cheaper.
Match every string `x` to `Function.update x 0 (!x 0)`, i.e. flip the first
coordinate.  This is an involution without fixed points, and the two strings
differ in exactly one coordinate, so the pair is a genuine `cube` edge.

1. Define the subgraph with `Adj x y := y = flip₀ x ∨ x = flip₀ y`.
2. `IsMatching`: each vertex has the unique neighbour `flip₀ x`.
3. `IsSpanning`: every vertex is covered by construction.

⚠ `hk : 2 ≤ k` is stronger than needed — `1 ≤ k` suffices for this argument, and
`k = 0` genuinely fails (one vertex, no edges).  The book's `k ≥ 2` is presumably
to keep the cube nontrivial.

## Status

`sorry`.  One of the more approachable exercises here.
-/
theorem cube_isPerfectMatching (k : ℕ) (hk : 2 ≤ k) :
    ∃ M : (cube k).Subgraph, M.IsPerfectMatching := by
  sorry

/-- Ex 5.1.1(b): number of perfect matchings of `K_{2n}` is `(2n)! / (2^n n!)`.

## Book statement (§5.1, p. 79) — verbatim

> (b) Find the number of different perfect matchings in $K_{2n}$ and $K_{n,n}$.

An exercise, so the book gives no proof; it does not even state the answers.

## In Lean notation

A perfect matching of `K_{2n}` partitions `2n` labelled objects into `n`
unordered pairs.  Lining them up gives `(2n)!` arrangements; each matching arises
from `2^n · n!` of them (swap within each pair, permute the pairs).  So the count
is `(2n)! / (2^n · n!)`, the double factorial `(2n-1)!! = 1 · 3 · 5 ⋯ (2n-1)`.

⚠ The Lean statement uses **natural-number division**.  It happens to be exact
here, but the proof cannot manipulate it as division — it must establish
`Nat.card … * (2 ^ n * n !) = (2 * n)!` and then divide, or the `Nat.div` will
obstruct every rewrite.

## Proof plan

1. Build an equiv between perfect matchings of `⊤` on `Fin (2n)` and the
   fixed-point-free involutions of `Fin (2n)`, or directly to unordered pair
   partitions.
2. Count by the greedy recursion instead of the division formula: the first
   vertex has `2n - 1` choices, leaving `K_{2n-2}`.  That gives
   `card (n+1) = (2n + 1) * card n`, an easy induction.
3. Prove `(2n)! = (2^n · n!) · (2n-1)!!` separately and combine, which is where
   the stated closed form comes from.

## Status

`sorry`.  Step 1 is the work; the arithmetic in steps 2–3 is routine but the
`Nat.div` in the statement makes it fiddlier than it looks.
-/
theorem card_perfectMatching_completeGraph (n : ℕ) :
    Nat.card {M : (⊤ : SimpleGraph (Fin (2 * n))).Subgraph // M.IsPerfectMatching}
      = (2 * n).factorial / (2 ^ n * n.factorial) := by
  sorry

/-- Ex 5.1.1(b): number of perfect matchings of `K_{n,n}` is `n!`.

## Book statement (§5.1, p. 79) — verbatim

> (b) Find the number of different perfect matchings in $K_{2n}$ and $K_{n,n}$.

An exercise, so the book gives no proof.

## In Lean notation

Every vertex of `X` may be matched to any vertex of `Y`, so a perfect matching is
exactly a bijection `X → Y`.  There are `n!` of those.

This is why the optimal assignment problem of §5.5 has `n!` candidate solutions
and brute force is hopeless — the book makes exactly that point on p. 94.

## Proof plan

1. Build `Equiv` between `{M // M.IsPerfectMatching}` on
   `completeBipartiteGraph (Fin n) (Fin n)` and `Equiv.Perm (Fin n)`:
   * forward — a perfect matching sends each `Sum.inl i` to a unique
     `Sum.inr (σ i)`; injectivity of `σ` is the matching property;
   * backward — from `σ`, take the subgraph with edges `s(inl i, inr (σ i))`.
2. `Nat.card (Equiv.Perm (Fin n)) = n !` is `Fintype.card_perm` plus
   `Fintype.card_fin`.

Cleaner than the `K_{2n}` count above, since the target is a standard Mathlib
type rather than an ad hoc partition count.

## Status

`sorry`.
-/
theorem card_perfectMatching_completeBipartite (n : ℕ) :
    Nat.card {M : (completeBipartiteGraph (Fin n) (Fin n)).Subgraph // M.IsPerfectMatching}
      = n.factorial := by
  sorry

/-- Ex 5.1.2: a tree has at most one perfect matching.

## Book statement (§5.1, p. 79) — verbatim

> **5.1.2** &nbsp; Show that a tree has at most one perfect matching.

An exercise, so the book gives no proof.

## In Lean notation

Suppose a tree had two perfect matchings `M ≠ M'`.  Every vertex meets at most
one edge of each, so every vertex of `M Δ M'` has degree one or two and its
components are alternating paths and even cycles.  Both matchings being perfect,
no vertex is an endpoint of such a path, so only cycles occur — impossible in an
acyclic graph.  Hence `M Δ M' = ∅`.

## Proof plan

✅ **The induction is much easier in Lean than the symmetric-difference
argument**, which would need the same "degree ≤ 2 implies paths-and-cycles"
structure lemma that `berge_maximum_matching` is blocked on.

Induct on `Fintype.card V`:
1. A nontrivial tree has a leaf (`Trees.lean`'s `tree_two_leaves` gives two).
2. Its single incident edge is forced into *any* perfect matching, since the leaf
   must be saturated and has only one neighbour.
3. So `M` and `M'` agree on that edge; delete both its ends and apply the
   inductive hypothesis to the remaining forest.

⚠ Step 3 leaves a *forest*, not a tree, so the induction should be stated for
acyclic graphs rather than trees — otherwise the hypothesis does not reapply.

## Status

`sorry`.
-/
theorem isTree_subsingleton_perfectMatching
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : G.IsTree)
    {M M' : G.Subgraph} (hM : M.IsPerfectMatching) (hM' : M'.IsPerfectMatching) :
    M = M' := by
  sorry

-- NOTE (this session): the Ex 5.2.3(a) block below was relocated verbatim from its
-- exercise-number position (after Ex 5.2.2(a)) because `completeBipartite_one_factorable`
-- (Ex 5.1.5(a)(i), next declaration) uses it and Lean has no forward references.

/-- Ex 5.2.3(a): every `k`-regular bipartite graph (`k > 0`) is 1-factorable.

## Book statement (§5.2, p. 83) — verbatim

> **5.2.3** For $k > 0$, show that
>
> *(a)* every $k$-regular bipartite graph is 1-factorable;

An exercise, so the book gives no proof.

## In Lean notation

Corollary 5.2 gives a perfect matching `M`.  Deleting its edges lowers every
degree by one, leaving a `(k-1)`-regular bipartite graph; iterate `k` times.

In chapter 6's language this is `χ'(G) = Δ(G)` for bipartite graphs — König's
edge-colouring theorem.  In scheduling terms, a balanced workload always splits
into `k` conflict-free rounds.

## Proof plan

Induction on `k`, generalising `G`:
1. `k = 0` — no edges, so the empty family works.  ⚠ The hypothesis `0 < k`
   blocks this base case, so the induction must be on an auxiliary statement
   allowing `k = 0`, with `hk` used only to rule out the degenerate conclusion.
2. `k > 0` — `marriage_theorem` gives a perfect matching `M`.
3. `G.deleteEdges M.edgeSet` is `(k-1)`-regular and still bipartite; apply the
   inductive hypothesis.
4. Assemble: `M` together with the `k-1` factors from step 3, checking pairwise
   disjointness and that the supremum is `⊤`.

## Status

Proved (kernel-checked, axioms `[propext, Classical.choice, Quot.sound]`),
exactly by the planned induction, with two technical refinements: the inner
induction is phrased over `(G.neighborSet v).ncard = t + 1` (instance-free
regularity, shifted so no `0 < k` side condition threads through), and the
factors of `G.deleteEdges M.edgeSet` are lifted back to `G.Subgraph` through an
existential packaged with `rfl`-transfer equations, so nothing downstream has to
unfold the lift.  Produces exactly `k` factors: `Fin.cons` of the deleted
perfect matching onto the `k − 1` lifted ones; `⨆ = ⊤` by per-edge case split.
-/
theorem regular_bipartite_one_factorable
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {X Y : Set V} (hbip : G.IsBipartiteWith X Y) {k : ℕ} (hk : 0 < k)
    (hreg : G.IsRegularOfDegree k) : G.IsKFactorable 1 := (by
  classical
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 1 := ⟨k - 1, by omega⟩
  have hncard : ∀ v, (G.neighborSet v).ncard = n + 1 := fun v =>
    (Set.ncard_eq_toFinset_card' (G.neighborSet v)).trans (hreg v)
  have main : ∀ t : ℕ, ∀ Gc : SimpleGraph V, Gc.IsBipartiteWith X Y →
      (∀ v, (Gc.neighborSet v).ncard = t + 1) →
      ∃ H : Fin (t + 1) → Gc.Subgraph, (∀ i, (H i).IsKFactor 1) ∧
        (∀ i j, i ≠ j → Disjoint (H i).edgeSet (H j).edgeSet) ∧ (⨆ i, H i) = ⊤ := by
    intro t
    induction t with
    | zero =>
      intro Gc hbipc hncardc
      refine ⟨fun _ => ⊤, fun i => ⟨fun v => Set.mem_univ v, fun v => ?_⟩,
        fun i j hij => absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) hij,
        le_antisymm le_top (le_iSup (fun _ : Fin (0 + 1) => (⊤ : Gc.Subgraph)) 0)⟩
      show ((⊤ : Gc.Subgraph).neighborSet v).ncard = 1
      rw [Subgraph.neighborSet_top]
      exact hncardc v
    | succ m ih =>
      intro Gc hbipc hncardc
      haveI : DecidableRel Gc.Adj := Classical.decRel _
      have hregc : Gc.IsRegularOfDegree (m + 1 + 1) := fun v =>
        (Set.ncard_eq_toFinset_card' (Gc.neighborSet v)).symm.trans (hncardc v)
      obtain ⟨M, hMpf⟩ := marriage_theorem Gc hbipc (Nat.succ_pos (m + 1)) hregc
      have hM1 : ∀ v : V, ∃ w, M.Adj v w ∧ ∀ y, M.Adj v y → y = w := fun v =>
        hMpf.1 (hMpf.2 v)
      choose p hp hup using hM1
      have hMns : ∀ v, M.neighborSet v = {p v} := by
        intro v
        ext w
        simp only [Subgraph.mem_neighborSet, Set.mem_singleton_iff]
        exact ⟨fun h => hup v w h, fun h => by rw [h]; exact hp v⟩
      have hM1fac : ∀ v, (M.neighborSet v).ncard = 1 := by
        intro v
        rw [hMns v]
        exact Set.ncard_singleton _
      have hbip' : (Gc.deleteEdges M.edgeSet).IsBipartiteWith X Y :=
        ⟨hbipc.disjoint, fun v w h => hbipc.mem_of_adj (deleteEdges_adj.mp h).1⟩
      have hNS : ∀ v, (Gc.deleteEdges M.edgeSet).neighborSet v
          = Gc.neighborSet v \ {p v} := by
        intro v
        ext w
        simp only [mem_neighborSet, deleteEdges_adj, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hadj, hnM⟩
          exact ⟨hadj, fun hw => hnM (by rw [hw]; exact Subgraph.mem_edgeSet.mpr (hp v))⟩
        · rintro ⟨hadj, hne⟩
          exact ⟨hadj, fun hmem => hne (hup v w (Subgraph.mem_edgeSet.mp hmem))⟩
      have hncard' : ∀ v, ((Gc.deleteEdges M.edgeSet).neighborSet v).ncard = m + 1 := by
        intro v
        have hpv : p v ∈ Gc.neighborSet v := M.adj_sub (hp v)
        have h1 : (Gc.neighborSet v \ {p v}).ncard + 1 = (Gc.neighborSet v).ncard :=
          Set.ncard_diff_singleton_add_one hpv (Set.toFinite _)
        have h2 := hncardc v
        rw [hNS v]
        omega
      obtain ⟨H', hH'fac, hH'disj, hH'top⟩ := ih (Gc.deleteEdges M.edgeSet) hbip' hncard'
      have hdisjM : ∀ N : (Gc.deleteEdges M.edgeSet).Subgraph,
          Disjoint M.edgeSet N.edgeSet := by
        intro N
        rw [Set.disjoint_left]
        intro e
        induction e using Sym2.ind with
        | _ a b =>
          intro heM heN
          exact (deleteEdges_adj.mp (N.adj_sub (Subgraph.mem_edgeSet.mp heN))).2 heM
      obtain ⟨L, hLverts, hLns, hLedge, hLadj⟩ :
          ∃ L : Fin (m + 1) → Gc.Subgraph,
            (∀ i, (L i).verts = (H' i).verts) ∧
            (∀ i v, (L i).neighborSet v = (H' i).neighborSet v) ∧
            (∀ i, (L i).edgeSet = (H' i).edgeSet) ∧
            (∀ i a b, (L i).Adj a b ↔ (H' i).Adj a b) :=
        ⟨fun i =>
          ⟨(H' i).verts, (H' i).Adj,
            fun h => (deleteEdges_adj.mp ((H' i).adj_sub h)).1,
            fun h => (H' i).edge_vert h, (H' i).symm⟩,
          fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => Iff.rfl⟩
      refine ⟨Fin.cons M L, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun i' => ?_) i
        · simp only [Fin.cons_zero]
          exact ⟨hMpf.2, hM1fac⟩
        · simp only [Fin.cons_succ]
          refine ⟨fun v => ?_, fun v => ?_⟩
          · rw [hLverts i']
            exact (hH'fac i').1 v
          · rw [hLns i' v]
            exact (hH'fac i').2 v
      · intro i j
        refine Fin.cases ?_ (fun i' => ?_) i
        · refine Fin.cases ?_ (fun j' => ?_) j
          · intro hij
            exact absurd rfl hij
          · intro hij
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [hLedge j']
            exact hdisjM (H' j')
        · refine Fin.cases ?_ (fun j' => ?_) j
          · intro hij
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [hLedge i']
            exact (hdisjM (H' i')).symm
          · intro hij
            simp only [Fin.cons_succ]
            rw [hLedge i', hLedge j']
            exact hH'disj i' j' fun h => hij (congrArg Fin.succ h)
      · refine le_antisymm le_top ⟨fun v _ => ?_, fun a b hab => ?_⟩
        · rw [Subgraph.verts_iSup]
          refine Set.mem_iUnion.mpr ⟨0, ?_⟩
          simp only [Fin.cons_zero]
          exact hMpf.2 v
        · rw [Subgraph.iSup_adj]
          have habG : Gc.Adj a b := (⊤ : Gc.Subgraph).adj_sub hab
          by_cases hMe : s(a, b) ∈ M.edgeSet
          · refine ⟨0, ?_⟩
            simp only [Fin.cons_zero]
            exact Subgraph.mem_edgeSet.mp hMe
          · have h1 : (Gc.deleteEdges M.edgeSet).Adj a b := deleteEdges_adj.mpr ⟨habG, hMe⟩
            have h2 : (⨆ i, H' i).Adj a b := by
              rw [hH'top]
              exact Subgraph.top_adj.mpr h1
            obtain ⟨i, hi⟩ := Subgraph.iSup_adj.mp h2
            refine ⟨i.succ, ?_⟩
            simp only [Fin.cons_succ]
            exact (hLadj i a b).mpr hi
  obtain ⟨H, hfac, hdisj, htop⟩ := main n G hbip hncard
  exact ⟨n + 1, H, hfac, hdisj, htop⟩
)

/-- Ex 5.1.5(a)(i): `K_{n,n}` is 1-factorable.

## Book statement (§5.1, p. 79) — verbatim

> $(a)^*$ Show that (i) $K_{n,n}$ and $K_{2n}$ are 1-factorable;

A starred exercise, so the book gives no proof.

## In Lean notation

Label both sides by `ZMod n`; for each `i`, let `Hᵢ` join `x_a` to `y_{a+i}` for
every `a`.  Each `Hᵢ` is a 1-factor, distinct `i` give edge-disjoint matchings,
and every edge `x_a y_b` occurs in exactly the one with `i = b - a`.

In chapter 6's language: `K_{n,n}` has chromatic index `n`, its minimum possible
value — the round-robin schedule for `n` workers and `n` jobs.

## Proof plan

1. Take `n` factors indexed by `Fin n`; `Hᵢ` has `Adj (inl a) (inr b) ↔ b = a + i`
   in `ZMod n` arithmetic.  ⚠ The carrier here is `Fin n`, so either transport
   along `Fin n ≃ ZMod n` or use `Fin.add` directly — the latter is fine since
   `Fin n` addition already wraps.
2. `IsKFactor 1`: each vertex has exactly one neighbour in `Hᵢ`, by the
   bijectivity of `a ↦ a + i`.
3. Pairwise edge-disjoint: `a + i = a + j` forces `i = j`.
4. `⨆ i, H i = ⊤`: given an edge `s(inl a, inr b)`, it lies in `H (b - a)`.

## Status

Proved (kernel-checked, axioms `[propext, Classical.choice, Quot.sound]`) — but
as a corollary of `regular_bipartite_one_factorable` (relocated above, see NOTE)
rather than by the explicit construction sketched below: `K_{n,n}` is `n`-regular
with bipartition `(range Sum.inl, range Sum.inr)`, so for `n > 0` the general
theorem applies; `n = 0` is the vacuous single-`⊤`-factor family on the empty
vertex type.
-/
theorem completeBipartite_one_factorable (n : ℕ) :
    (completeBipartiteGraph (Fin n) (Fin n)).IsKFactorable 1 := (by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, fun _ => ⊤,
      fun i => ⟨fun v => Set.mem_univ v, fun v => isEmptyElim v⟩,
      fun i j hij => absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) hij,
      le_antisymm le_top
        (le_iSup (fun _ : Fin 1 => (⊤ : (completeBipartiteGraph (Fin 0) (Fin 0)).Subgraph)) 0)⟩
  · haveI : DecidableRel (completeBipartiteGraph (Fin n) (Fin n)).Adj := fun a b =>
      decidable_of_iff _ (completeBipartiteGraph_adj _ _ a b).to_iff.symm
    have hbip : (completeBipartiteGraph (Fin n) (Fin n)).IsBipartiteWith
        (Set.range Sum.inl) (Set.range Sum.inr) := by
      constructor
      · rw [Set.disjoint_left]
        rintro v ⟨a, rfl⟩ ⟨b, hb⟩
        exact Sum.noConfusion hb
      · intro v w hvw
        cases v with
        | inl a =>
          cases w with
          | inl b => simp at hvw
          | inr b => exact Or.inl ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
        | inr a =>
          cases w with
          | inl b => exact Or.inr ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
          | inr b => simp at hvw
    have hreg : (completeBipartiteGraph (Fin n) (Fin n)).IsRegularOfDegree n := by
      intro v
      cases v with
      | inl a =>
        have hfin : (completeBipartiteGraph (Fin n) (Fin n)).neighborFinset (Sum.inl a)
            = Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩ := by
          ext w
          cases w with
          | inl b => simp [mem_neighborFinset]
          | inr b => simp [mem_neighborFinset]
        rw [← card_neighborFinset_eq_degree, hfin, Finset.card_map, Finset.card_univ,
          Fintype.card_fin]
      | inr a =>
        have hfin : (completeBipartiteGraph (Fin n) (Fin n)).neighborFinset (Sum.inr a)
            = Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
          ext w
          cases w with
          | inl b => simp [mem_neighborFinset]
          | inr b => simp [mem_neighborFinset]
        rw [← card_neighborFinset_eq_degree, hfin, Finset.card_map, Finset.card_univ,
          Fintype.card_fin]
    exact regular_bipartite_one_factorable _ hbip hn hreg
)

/-- Ex 5.1.5(a)(i): `K_{2n}` is 1-factorable.

## Book statement (§5.1, p. 79) — verbatim

> $(a)^*$ Show that (i) $K_{n,n}$ and $K_{2n}$ are 1-factorable;

A starred exercise, so the book gives no proof.

## In Lean notation

The classical round-robin schedule.  Fix one vertex at the centre and arrange the
other `2n - 1` in a circle.  In round `i`, match the centre with circle vertex
`i` and pair the remaining circle vertices symmetrically about the line through
it.  Rotating gives `2n - 1` rounds, each a perfect matching, together using
every edge exactly once.

So `2n` players can be scheduled in `2n - 1` rounds with every pair meeting once.
This fails for odd order, where no perfect matching exists at all.

## Proof plan

1. Split the carrier as `Fin (2n) ≃ Unit ⊕ ZMod (2n - 1)`, the centre plus the
   circle.  ⚠ This re-indexing is the fiddliest part and needs `n ≥ 1`; at
   `n = 0` the carrier is empty and the statement holds vacuously with zero
   factors, so that case should be split off first.
2. Round `i : ZMod (2n-1)` matches `centre ↔ i`, and `a ↔ 2i - a` for `a ≠ i` on
   the circle.  Well defined because `2n - 1` is odd, so `a ↦ 2i - a` has `i` as
   its unique fixed point.
3. `IsKFactor 1` per round, edge-disjointness, and total coverage as in the
   `K_{n,n}` case.

⚠ Step 2's "`2n - 1` is odd, so halving is unique" is exactly where the argument
would break for `K_{2n+1}`, and is worth isolating as a lemma.

## Status

`sorry`.  Harder than the `K_{n,n}` case purely because of the centre/circle
re-indexing.
-/
theorem completeGraph_even_one_factorable (n : ℕ) :
    (⊤ : SimpleGraph (Fin (2 * n))).IsKFactorable 1 := by
  sorry

/-- Ex 5.1.5(c): `ν` even and `δ ≥ ν/2 + 1` ⇒ `G` has a 3-factor (via Dirac; blocked on ch4).
NOTE: `δ ≥ ν/2 + 1` stated as `ν + 2 ≤ 2δ` to avoid ℕ division.

## Book statement (§5.1, p. 80) — verbatim

> (c) Using Dirac's theorem (4.3), show that if $G$ is simple, with $\nu$ even and
> $\delta \geq (\nu/2)+1$, then $G$ has a 3-factor.

An exercise, so the book gives no proof.

## In Lean notation

`δ ≥ ν/2 + 1` is one better than Dirac's threshold, so Theorem 4.3 gives a
Hamilton cycle `C`.  With `ν` even, `C` is an even cycle whose edges split
alternately into two perfect matchings.  Removing `C`'s edges drops every degree
by `2`, leaving enough for a second Hamilton cycle; combining the 2-factor `C`
with a 1-factor from the second gives degree `3` everywhere.

`δ ≥ ν/2 + 1` is formalised as `ν + 2 ≤ 2δ` to stay in the natural numbers.

## Proof plan

1. Dirac (`EulerHamilton.lean`'s `dirac_hamiltonian`) gives a Hamilton cycle `C`.
2. `ν` even ⇒ `C` even ⇒ its edges 2-colour alternately into perfect matchings
   `M₁`, `M₂`.
3. Delete `C`'s edges; minimum degree is now `≥ δ - 2 ≥ ν/2 - 1`.  ⚠ That is
   *one short* of Dirac's threshold `ν/2`, so Theorem 4.3 does **not** reapply
   directly — the second Hamilton cycle needs a separate argument, or the
   3-factor must be assembled as `C ∪ M` for a perfect matching `M` obtained
   another way (e.g. from Corollary 5.2 or Tutte).
4. Verify the union is spanning and 3-regular.

⚠ This file **does not import `EulerHamilton.lean`**, so `dirac_hamiltonian` is
not in scope; either add the import or restate Dirac locally.

## Status

`sorry`, blocked on chapter 4's Dirac theorem (itself `sorry`) and on the gap at
step 3.
-/
theorem exists_three_factor_of_minDegree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hν : Even (Fintype.card V)) (hδ : Fintype.card V + 2 ≤ 2 * G.minDegree) :
    ∃ H : G.Subgraph, H.IsKFactor 3 := by
  sorry

/-- Ex 5.1.6*: `K_{2n+1}` decomposes into `n` connected 2-factors (Walecki).

## Book statement (§5.1, p. 80) — verbatim

> 5.1.6\* Show that $K_{2n+1}$ can be expressed as the union of $n$ connected
> 2-factors $(n \geq 1)$.

A starred exercise, so the book gives no proof.

## In Lean notation

A connected 2-factor is precisely a Hamilton cycle — a spanning connected
2-regular subgraph must be one cycle through every vertex.  So this asks for a
decomposition of `K_{2n+1}`'s edges into Hamilton cycles.

The count works: `K_{2n+1}` has `n(2n+1)` edges and each Hamilton cycle uses
`2n + 1`, so exactly `n` cycles are needed.

The odd-order companion to 5.1.5(a)(i): odd complete graphs decompose into
Hamilton cycles, even ones into perfect matchings.

## Proof plan

Walecki's construction: arrange `2n` vertices in a circle with one at the centre;
take the zig-zag Hamilton path across the circle plus the two edges joining its
ends to the centre; rotate `n` times.

1. Re-index `Fin (2n+1) ≃ Unit ⊕ ZMod (2n)`.
2. Cycle `i` is the zig-zag `i, i+1, i-1, i+2, i-2, …` on the circle, closed
   through the centre.
3. Edge-disjointness: circle edges are classified by the *difference* of their
   endpoints, and the zig-zag uses each difference exactly once per rotation.
4. Coverage by the count above.

⚠ Unlike `IsKFactorable`, this statement spells the decomposition out inline
(with the added `Connected` conjunct), so it does not reuse that definition.

## Status

`sorry`.  The hardest of the three factorisation exercises — step 3 needs the
difference-classification argument set up carefully.
-/
theorem completeGraph_odd_two_factorable (n : ℕ) (hn : 1 ≤ n) :
    ∃ H : Fin n → (⊤ : SimpleGraph (Fin (2 * n + 1))).Subgraph,
      (∀ i, (H i).IsKFactor 2 ∧ (H i).Connected) ∧
      (∀ i j, i ≠ j → Disjoint (H i).edgeSet (H j).edgeSet) ∧ (⨆ i, H i) = ⊤ := by
  sorry

/-- Ex 5.2.2(a): bipartite perfect-matching criterion.  ⚠ `X ∪ Y = univ` is REQUIRED here.

## Book statement (§5.2, p. 83) — verbatim

> **5.2.2** *(a)* Show that a bipartite graph $G$ has a perfect matching if and
> only if $|N(S)| \geq |S|$ for all $S \subseteq V$.

An exercise, so the book gives no proof.

## In Lean notation

Hall's Theorem 5.2 gives a matching saturating `X` from the condition on subsets
of `X` alone.  Demanding it for *all* subsets of `V` is symmetric in `X` and `Y`,
so it yields matchings saturating each side; together these force `|X| = |Y|` and
a perfect matching.

⚠ `hcov : X ∪ Y = Set.univ` is **required** and has no counterpart in the book's
wording, which takes "bipartition" to cover all vertices by definition.
Mathlib's `IsBipartiteWith` does not, so without `hcov` the bipartition could
miss vertices that no matching could ever saturate.

## Proof plan

1. (⇒) A perfect matching gives an injection `S → N(S)` for every `S ⊆ V`, by
   sending each vertex to its partner.
2. (⇐) Apply the condition to subsets of `X` and invoke
   `hall_bipartite_matching` for a matching `M₁` saturating `X`; symmetrically
   get `M₂` saturating `Y`.
3. Both give `|X| ≤ |Y|` and `|Y| ≤ |X|`, so `|X| = |Y|`; then `M₁` saturating
   `X` with `|X| = |Y|` and `hcov` makes `M₁` perfect — the same counting step
   flagged on `marriage_theorem`.

## Status

Proved (kernel-checked, axioms `[propext, Classical.choice, Quot.sound]`).
(⇒) is the partner-injection idiom from `hall_bipartite_matching`, with
saturation supplied by `IsSpanning`; (⇐) is Mathlib's
`exists_isPerfectMatching_of_forall_ncard_le` directly.  Note `hcov` turned out
to be **unused**: the global Hall condition itself rules out isolated vertices,
which with `hbip` recovers coverage, so the ⚠ above was overcautious.  The
hypothesis is kept (frozen statement); a future simplify pass could drop it.
-/
theorem bipartite_perfectMatching_iff
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {X Y : Set V} (hbip : G.IsBipartiteWith X Y) (hcov : X ∪ Y = Set.univ) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∀ S : Set V, S.ncard ≤ (⋃ v ∈ S, G.neighborSet v).ncard := (by
  classical
  constructor
  · rintro ⟨M, hM⟩ S
    have hpick : ∀ v ∈ S, ∃ w, M.Adj v w := fun v _ => (hM.1 (hM.2 v)).exists
    choose! g hg using hpick
    have hmem : ∀ v ∈ S, g v ∈ ⋃ u ∈ S, G.neighborSet u := fun v hv =>
      Set.mem_biUnion hv (M.adj_sub (hg v hv))
    have hinj : Set.InjOn g S := by
      intro v₁ hv₁ v₂ hv₂ heq
      have h1 : M.Adj (g v₁) v₁ := (hg v₁ hv₁).symm
      have h2 : M.Adj (g v₁) v₂ := by rw [heq]; exact (hg v₂ hv₂).symm
      exact hM.1.eq_of_adj_left h1 h2
    exact Set.ncard_le_ncard_of_injOn g hmem hinj (Set.toFinite _)
  · exact fun h => exists_isPerfectMatching_of_forall_ncard_le hbip h
)

/-- Ex 5.2.3(b)*: every `2k`-regular graph is 2-factorable (Petersen; blocked on ch4 Euler tours).

## Book statement (§5.2, p. 83) — verbatim

> *(b)\** every $2k$-regular graph is 2-factorable. $\qquad$ (J. Petersen)

A starred exercise, so the book gives no proof.

## In Lean notation

Every degree is even, so Theorem 4.1 gives each component an Euler tour.
Traverse it and orient each edge in the direction of travel; every vertex then
has in-degree `k` and out-degree `k`, since the tour enters and leaves it `k`
times.  Build the bipartite "tail/head" double cover, joining tail `u` to head
`v` for each oriented edge `u → v`.  That graph is `k`-regular, hence
1-factorable by part (a); translating each perfect matching back gives a spanning
subgraph with one in-edge and one out-edge per vertex — a 2-factor.

## Proof plan

1. Euler tour per component — ⚠ this needs `euler_tour_iff_no_odd_degree` from
   `EulerHamilton.lean`, which this file **does not import** and which is itself
   `sorry`.
2. Orient along the tour; formalising "orientation" needs a directed structure
   this file does not have.  Practically: define the tail/head bipartite graph
   directly from the tour's edge list.
3. Apply `regular_bipartite_one_factorable` (part (a)).
4. Translate matchings back to 2-factors.

## Status

`sorry`, and doubly blocked: on chapter 4's Euler theorem and on part (a).  The
orientation step at 2 has no supporting infrastructure in this file at all,
making this the most infrastructure-hungry exercise in the chapter.

⚠ **Statement repaired (this session, user-authorized)** — `hk : 0 < k` added.
Without it the statement was **false at `k = 0`**: an edgeless graph on a nonempty
carrier is `0`-regular (hence `2·0`-regular), but `IsKFactorable 2` fails — with
zero factors `⨆ (i : Fin 0), H i = ⊥` whose `verts = ∅ ≠ Set.univ = ⊤.verts`, and
any factor would need degree `2` in an edgeless graph.  Petersen's theorem is the
`k ≥ 1` content.
-/
theorem regular_two_factorable
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 0 < k) (hreg : G.IsRegularOfDegree (2 * k)) : G.IsKFactorable 2 := by
  sorry

/-- Ex 5.2.5: König's theorem, matrix (line-cover) form.

## Book statement (§5.2, p. 83) — verbatim

> **5.2.5** A *line* of a matrix is a row or a column of the matrix. Show that the
> minimum number of lines containing all the 1's of a $(0, 1)$-matrix is equal to
> the maximum number of 1's, no two of which are in the same line.

An exercise, so the book gives no proof.

## In Lean notation

König's Theorem 5.3 in matrix dress.  A vertex per row and per column, joining
row `i` to column `j` when `A i j = true`.  Lines covering all the `1`s are a
vertex covering; `1`s no two sharing a line are a matching.

The `IsLeast`/`IsGreatest` hypotheses supply the two optima as *given*, so this
statement only has to equate them.  "No two in the same line" is rendered as the
pair of `InjOn` conditions on `Prod.fst` and `Prod.snd`.

## Proof plan

1. Build the bipartite graph on `Fin m ⊕ Fin n` with
   `Adj (inl i) (inr j) ↔ A i j = true`.
2. Translate `hc` into a minimum covering of that graph: `R ∪ C` maps to
   `inl '' R ∪ inr '' C`, and the covering condition matches.
3. Translate `hd` into a maximum matching: `S` maps to the edge set
   `{s(inl p.1, inr p.2) | p ∈ S}`, and the two `InjOn`s are exactly
   `IsMatching`.
4. `konig_matching_covering` equates them; transport back through the
   translations.

## Status

`sorry`, depends on `konig_matching_covering`.  The mathematics is entirely in
that theorem — everything here is the encode/decode, which is nonetheless a
substantial amount of `Finset`-to-`Subgraph` plumbing.
-/
theorem konig_matrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool)
    {c : ℕ} (hc : IsLeast {k | ∃ (R : Finset (Fin m)) (C : Finset (Fin n)),
        R.card + C.card = k ∧ ∀ i j, A i j = true → i ∈ R ∨ j ∈ C} c)
    {d : ℕ} (hd : IsGreatest {k | ∃ S : Finset (Fin m × Fin n), S.card = k ∧
        (∀ p ∈ S, A p.1 p.2 = true) ∧ (S : Set (Fin m × Fin n)).InjOn Prod.fst ∧
        (S : Set (Fin m × Fin n)).InjOn Prod.snd} d) :
    c = d := by
  sorry

/-- Ex 5.2.6(a): the König–Ore defect formula (stated additively to avoid ℕ subtraction).

## Book statement (§5.2, p. 84) — verbatim

> 5.2.6 (a) Prove the following generalisation of Hall's theorem (5.2): if $G$ is
> a bipartite graph with bipartition $(X, Y)$, the number of edges in a maximum
> matching of $G$ is
> $$|X| - \max_{S \subseteq X} \{|S| - |N(S)|\}$$
> (D. König, O. Ore)

An exercise, so the book gives no proof.

## In Lean notation

Hall's theorem says a matching saturating `X` exists exactly when
`|S| - |N(S)| ≤ 0` for all `S ⊆ X`.  The defect formula quantifies failure: the
largest `|S| - |N(S)|`, the **deficiency**, is exactly how many vertices of `X`
a maximum matching must leave unsaturated.  Hall is the zero-deficiency case.

Formalised additively as `|M| + deficiency = |X|` to avoid ℕ subtraction on the
outside.

⚠ But the *inner* `S.ncard - (⋃ …).ncard` is still natural subtraction, so it
truncates to `0` exactly when Hall's condition holds at `S` — which is what makes
the `⨆` compute the book's `max{…}` correctly only because the book's max is
also effectively taken against `0` (via `S = ∅`).  This is a happy accident
rather than a faithful rendering, and is worth re-checking when the proof is
attempted.

## Proof plan

1. Take `S₀` attaining the supremum (finite, so attained).
2. `≤`: any matching leaves at least `|S₀| - |N(S₀)|` vertices of `X`
   unsaturated, since `S₀`'s partners all lie in `N(S₀)`.
3. `≥`: add `deficiency` new vertices to `Y`, joined to all of `X`; the enlarged
   graph satisfies Hall's condition, so has a matching saturating `X`; restrict.
4. Combine.

## Status

`sorry`, depends on `hall_bipartite_matching`.
-/
theorem konig_ore_defect
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {X Y : Set V} (hbip : G.IsBipartiteWith X Y)
    {M : G.Subgraph} (hM : M.IsMaximumMatching) :
    M.edgeSet.ncard + (⨆ S ∈ {S | S ⊆ X}, (S.ncard - (⋃ v ∈ S, G.neighborSet v).ncard))
      = X.ncard := by
  sorry

/-- Ex 5.2.6(b): simple, `|X| = |Y| = n`, `ε > (k−1)n` ⇒ a matching of size `k`.

## Book statement (§5.2, p. 84) — verbatim

> (b) Deduce that if $G$ is simple with $|X| = |Y| = n$ and
> $\varepsilon > (k-1)n$, then $G$ has a matching of cardinality $k$.

An exercise, so the book gives no proof.

## In Lean notation

By the defect formula, a maximum matching smaller than `k` forces some `S ⊆ X`
with large `|S| - |N(S)|`.  Every edge meeting `S` then ends inside the small set
`N(S)`, and simplicity caps the total edge count at `(k-1)n` — contradiction.

Equivalently, via König: a covering of size `< k` caps `ε` at `(k-1)n`, since
each covering vertex has degree at most `n`.

## Proof plan

The König route is shorter than the defect route:
1. `by_contra`: every matching has fewer than `k` edges, so a maximum matching
   `M` has `|M| ≤ k - 1`.
2. `konig_matching_covering` gives a covering `K` with `|K| = |M| ≤ k - 1`.
3. Every edge meets `K`, and each vertex of `K` has degree `≤ n` (its neighbours
   lie in the opposite side, of size `n`).  So `ε ≤ (k-1)n`, contradicting `hε`.

⚠ The statement asks for a matching of cardinality *exactly* `k`, but the
argument naturally produces one of size `≥ k`.  Extracting exactly `k` needs a
sub-matching step — take any `k` edges of a larger matching, which is still a
matching.  Cheap, but not automatic.

## Status

`sorry`, depends on `konig_matching_covering` (or on `konig_ore_defect`).
-/
theorem exists_matching_card_eq_of_card_edges_gt
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {X Y : Set V} (hbip : G.IsBipartiteWith X Y) {n k : ℕ}
    (hX : X.ncard = n) (hY : Y.ncard = n)
    (hε : (k - 1) * n < G.edgeFinset.card) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = k := by
  sorry

/-- Ex 5.2.8(a): a (rectangular) doubly stochastic matrix is necessarily square. — RESTATED
(Mathlib's `doublyStochastic` is square by type, so the literal statement is vacuous).

## Book statement (§5.2, p. 84) — verbatim

> **5.2.8\*** A non-negative real matrix $\mathbf{Q}$ is *doubly stochastic* if
> the sum of the entries in each row of $\mathbf{Q}$ is 1 and the sum of the
> entries in each column of $\mathbf{Q}$ is 1. [...] Show that
>
> (a) every doubly stochastic matrix is necessarily square;

A starred exercise, so the book gives no proof.

## In Lean notation

Sum every entry two ways.  By rows: `1` each, so `m` in total.  By columns: `1`
each, so `n`.  Hence `m = n`.

⚠ **Restated, not transcribed.**  Mathlib's `doublyStochastic` is square *by
type*, so the literal statement would be vacuous.  This version takes a genuinely
rectangular `Matrix m n ℝ` with the two summation hypotheses given explicitly,
which is what the exercise actually asks.

Note the non-negativity hypothesis is not needed for this part and is omitted.

## Proof plan

`Fintype.card m = ∑ i, 1 = ∑ i, ∑ j, Q i j = ∑ j, ∑ i, Q i j = ∑ j, 1 = Fintype.card n`,
using `Finset.sum_comm` for the middle step and `hrow`/`hcol` at the ends.

⚠ The two sides are `ℕ` but the sums are `ℝ`, so the chain lives in `ℝ` and needs
`Nat.cast_injective` at the end.

## Status

`sorry`.  Genuinely easy — a `Finset.sum_comm` plus casts.
-/
theorem doublyStochastic_card_eq {m n : Type*} [Fintype m] [Fintype n]
    (Q : Matrix m n ℝ) (hrow : ∀ i, ∑ j, Q i j = 1) (hcol : ∀ j, ∑ i, Q i j = 1) :
    Fintype.card m = Fintype.card n := (by
  have h : (Fintype.card m : ℝ) = (Fintype.card n : ℝ) := by
    calc (Fintype.card m : ℝ) = ∑ _i : m, (1 : ℝ) := by simp
      _ = ∑ i, ∑ j, Q i j := Finset.sum_congr rfl fun i _ => (hrow i).symm
      _ = ∑ j, ∑ i, Q i j := Finset.sum_comm
      _ = ∑ _j : n, (1 : ℝ) := Finset.sum_congr rfl fun j _ => hcol j
      _ = (Fintype.card n : ℝ) := by simp
  exact Nat.cast_injective h
)

/-- Ex 5.2.9: a common transversal of the left and right cosets of a subgroup (P. Hall).
NOTE: this is one of several faithful renderings; the outline flags the exact shape as
likely to need revision.

## Book statement (§5.2, p. 84) — verbatim

> 5.2.9 Let $H$ be a finite group and let $K$ be a subgroup of $H$. Show that
> there exist elements $h_1, h_2, \ldots, h_n \in H$ such that
> $h_1K, h_2K, \ldots, h_nK$ are the left cosets of $K$ and
> $Kh_1, Kh_2, \ldots, Kh_n$ are the right cosets of $K$.
>
> (P. Hall)

An exercise, so the book gives no proof.

## In Lean notation

Left and right cosets each partition `H` into `n = [H : K]` blocks of size `|K|`.
The claim: one list of `n` elements represents *both* partitions simultaneously.

Hall again — put left cosets on one side, right cosets on the other, joining `aK`
to `Kb` when they intersect.  All cosets having size `|K|` makes this graph
regular, so Corollary 5.2 gives a perfect matching; choosing an element from each
matched intersection is the common transversal.

⚠ **Statement repaired (this session, user-authorized).**  The previous rendering
asserted `Function.Bijective` of the coset maps *into the full type `Set H`* —
surjectivity onto every subset of `H`, including `∅`, which no coset is.  Even the
trivial group refuted it.  The repaired form says exactly what P. Hall's exercise
says: the `n` maps `i ↦ hᵢ • K` are injective with range the set of left cosets,
and simultaneously `i ↦ op hᵢ • K` are injective with range the set of right
cosets.

## Proof plan

1. Build the bipartite graph on left cosets ⊕ right cosets, adjacency = nonempty
   intersection.
2. Regularity: `|aK ∩ Kb|` is either `0` or a constant, and each `aK` meets
   exactly `|K|` right cosets counted with multiplicity — this is the group-theory
   content and needs `Subgroup.card_leftCoset` style lemmas.
3. `marriage_theorem` gives a perfect matching.
4. Choose `hᵢ` from each matched intersection.

## Status

`sorry`, depends on `marriage_theorem`, and the statement shape needs review
first.
-/
theorem exists_common_coset_transversal {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    (K : Subgroup H) [DecidablePred (· ∈ K)] :
    ∃ (n : ℕ) (h : Fin n → H),
      Function.Injective (fun i => (h i : H) • (K : Set H)) ∧
      Set.range (fun i => (h i : H) • (K : Set H)) = {C : Set H | ∃ a : H, C = a • (K : Set H)} ∧
      Function.Injective (fun i => MulOpposite.op (h i : H) • (K : Set H)) ∧
      Set.range (fun i => MulOpposite.op (h i : H) • (K : Set H))
        = {C : Set H | ∃ a : H, C = MulOpposite.op a • (K : Set H)} := by
  sorry

/-- Ex 5.3.2: a `(k−1)`-edge-connected `k`-regular graph with `ν` even has a perfect matching.

## Book statement (§5.3, p. 88) — verbatim

> **5.3.2** Prove the following generalisation of corollary 5.4: if $G$ is a
> $(k-1)$-edge-connected $k$-regular graph with $\nu$ even, then $G$ has a perfect
> matching.

An exercise, so the book gives no proof.

## In Lean notation

Petersen's argument at general `k`.  For `S ⊂ V` with odd components `Gᵢ` of
`G - S` and `mᵢ` the edges from `Gᵢ` to `S`: regularity gives
`mᵢ = kν(Gᵢ) - 2ε(Gᵢ)`, of the same parity as `kν(Gᵢ)`.  Those edges form an edge
cut, so `(k-1)`-edge-connectivity gives `mᵢ ≥ k - 1`, and parity upgrades that to
`mᵢ ≥ k` where needed.  Summing,
`k · o(G - S) ≤ ∑ mᵢ ≤ ∑_{v ∈ S} d(v) = k|S|`.

Corollary 5.4 is the case `k = 3`: a bridgeless cubic graph is 2-edge-connected.

## Proof plan

Structurally identical to `petersen_three_regular_bridgeless`, with `3` replaced
by `k` and "no cut edge" by `hconn`.  Both should be written once and specialised,
rather than proved twice.

1. `tutte_perfect_matching` (⇐); fix `S`.
2. Per odd component, `mᵢ` has the parity of `k · ν(Gᵢ)`.
3. `mᵢ ≥ k - 1` from `hconn`, since the boundary is an edge cut; upgrade to
   `mᵢ ≥ k` by parity when `k - 1` has the wrong parity.
4. Sum and divide by `k` (using `hk`).

⚠ The `hν : Even (Fintype.card V)` hypothesis is not used by this argument —
Tutte's condition alone gives the matching.  It is presumably in the book's
statement to rule out the vacuous odd case; worth checking whether it is
genuinely needed at step 3.

## Status

`sorry`, depends on `tutte_perfect_matching` and shares the edge-boundary
infrastructure gap flagged on Corollary 5.4.
-/
theorem perfectMatching_of_edgeConnected_regular
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 0 < k) (hreg : G.IsRegularOfDegree k)
    (hconn : k - 1 ≤ G.edgeConnectivity) (hν : Even (Fintype.card V)) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  sorry

/-- Ex 5.3.3: a tree has a perfect matching iff `o(G − v) = 1` for every vertex `v`.

## Book statement (§5.3, p. 88) — verbatim

> **5.3.3** Show that a tree $G$ has a perfect matching if and only if
> $o(G-v)=1$ for all $v \in V$. (V. Chungphaisan)

An exercise, so the book gives no proof.

## In Lean notation

Tutte's condition quantifies over all `S`, but for trees the singletons already
decide it.

(⇒) The partner of `v` lies in one component of `G - v`, and a parity count shows
exactly one component is odd.

(⇐) `o(G - v) = 1` for every `v` is Tutte's condition at singletons, and
acyclicity makes that enough: build greedily from the leaves, each leaf forced to
match its unique neighbour.

Combined with exercise 5.1.2, a tree's perfect matching — when it exists — is
unique and locally detectable.

## Proof plan

⚠ The (⇐) direction does **not** follow from `tutte_perfect_matching` alone:
Tutte needs the condition at *all* `S`, and this hypothesis supplies only
singletons.  Acyclicity is what bridges the gap, so the greedy leaf induction is
the actual proof and Tutte is not used.

1. (⇒) From a perfect matching `M` and any `v`: `M` restricted to each component
   of `G - v` is perfect except in the one containing `v`'s partner, which has
   odd order.  Parity gives exactly one odd component.
2. (⇐) Induct on `Fintype.card V` as in `isTree_subsingleton_perfectMatching`:
   take a leaf `u` with neighbour `w`; `o(G - u) = 1` forces `w` to be matched to
   `u`; delete both and recurse.  ⚠ Again the remainder is a *forest*, so the
   induction should be stated for forests.

## Status

`sorry`.
-/
theorem isTree_perfectMatching_iff
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : G.IsTree) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∀ v : V, ((⊤ : G.Subgraph).deleteVerts {v}).coe.oddComponents.ncard = 1 := by
  sorry

/-- Ex 5.3.4*: the Berge–Tutte defect formula (stated additively to avoid ℕ subtraction).

## Book statement (§5.3, p. 88) — verbatim

> **5.3.4\*** Prove the following generalisation of Tutte's theorem (5.4): the
> number of edges in a maximum matching of $G$ is $\frac{1}{2}(\nu-d)$, where
> $$d = \max_{S \subseteq V}\{o(G-S)-|S|\}.$$
> (C. Berge)

A starred exercise, so the book gives no proof.

## In Lean notation

Tutte says a perfect matching exists exactly when `o(G - S) - |S| ≤ 0` for all
`S`.  Berge's formula quantifies failure: the maximum, the **deficiency** `d`, is
exactly how many vertices a maximum matching leaves unsaturated; the remaining
`ν - d` pair up.

`d = 0` recovers Theorem 5.4.  The general-graph analogue of the König–Ore defect
formula (5.2.6(a)).

Formalised additively as `2|M| + d = ν` to avoid ℕ subtraction on the outside.

⚠ Same caveat as `konig_ore_defect`: the *inner* `oddComponents.ncard - S.ncard`
is still natural subtraction and truncates at `0`.  Here that is actually
*correct*, since `S = ∅` always contributes `o(G) - 0 ≥ 0` and the book's max is
over a set containing a non-negative value — but it should be re-verified rather
than assumed.

## Proof plan

1. `≤` direction: for the maximising `S`, each odd component of `G - S` must
   leave at least one vertex unmatched or matched into `S`, giving at least
   `o(G - S) - |S|` unsaturated vertices.
2. `≥` direction: the standard reduction adds `d` universal vertices to `G`; the
   enlarged graph satisfies Tutte's condition, so has a perfect matching, and
   deleting the added vertices leaves a matching of the required size.
3. Combine with `2|M| + unsaturated = ν`.

## Status

`sorry`, depends on `tutte_perfect_matching` (cheap) but step 2's graph
enlargement is real work.
-/
theorem berge_tutte_defect
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMaximumMatching) :
    2 * M.edgeSet.ncard + (⨆ S : Set V, (((⊤ : G.Subgraph).deleteVerts S).coe.oddComponents.ncard
      - S.ncard)) = Fintype.card V := by
  sorry

/-- Ex 5.3.5(b): `ν` even, `δ < ν/2`, and a large edge count ⇒ a perfect matching.

## Book statement (§5.3, p. 88) — verbatim

> ($b$) Let $G$ be simple, with $\nu$ even and $\delta < \nu/2$. Show that if
> $\varepsilon > \binom{\delta}{2} + \binom{\nu-2\delta-1}{2} + \delta(\nu-\delta)$,
> then $G$ has a perfect matching.

An exercise, so the book gives no proof.

## In Lean notation

An edge-count sufficient condition, in the spirit of Corollary 4.6 for
hamiltonicity.  The threshold is the edge count of the densest simple graph on
`ν` vertices with minimum degree `δ` that still violates Tutte's condition: a
`δ`-set `S` whose removal leaves too many odd components, plus as many edges as
can be packed around it.  Exceeding it leaves no room to violate Tutte.

Part (a) — "characterise the maximal simple graphs which have no perfect
matching" — has no propositional content and is dropped; the book's answer is
recorded in the dropped-items section at the end of this file.

## Proof plan

1. `by_contra`; `tutte_perfect_matching` gives a violating `S` with
   `o(G - S) > |S|`.
2. Parity: `ν` even forces `o(G - S)` and `|S|` to have the same parity, so
   `o(G - S) ≥ |S| + 2`.
3. `δ ≤ |S|` — a vertex in an odd component of size `1` has all its neighbours in
   `S`, and `δ < ν/2` guarantees such a component exists.
4. Bound `ε` above by the stated expression: edges within `S`
   (`C(δ,2)` after step 3), edges within the largest component
   (`C(ν-2δ-1,2)`), and edges meeting `S` (`δ(ν-δ)`).
5. Contradict `hε`.

⚠ Step 4's split is where the exact form of the threshold comes from, and getting
the three terms to line up with the book's requires care about double-counted
edges.

## Status

`sorry`.  Depends on `tutte_perfect_matching`; the counting in step 4 is the
substance.
-/
theorem perfectMatching_of_card_edges_gt
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hν : Even (Fintype.card V)) (hδ : 2 * G.minDegree < Fintype.card V)
    (hε : Nat.choose G.minDegree 2 + Nat.choose (Fintype.card V - 2 * G.minDegree - 1) 2
            + G.minDegree * (Fintype.card V - G.minDegree) < G.edgeFinset.card) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  sorry

-- DROPPED / N/A per outline (not statable or not a proposition):
--   Ex 5.1.5(b): figure omitted from source — unstatable.
--   Ex 5.3.5(a): "characterise …" — no proposition in the text.
--   Ex 5.4.1, Ex 5.5.1: prose / a specific computation.
--   Ex 5.2.7, Ex 5.3.1: alternative derivations of Thm 5.2, not new statements.
--   `IsAlternatingTree`, Hungarian method, Kuhn–Munkres: procedural (would be `def … := sorry`).

end SimpleGraph
