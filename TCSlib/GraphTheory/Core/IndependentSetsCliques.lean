import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Convex.Hull

/-!
# Bondy & Murty, *Graph Theory with Applications* — Chapter 7: Independent Sets and Cliques

Sorry-skeleton extracted from `papers/bondy-murty-ch7-independent-sets-cliques.md`.

Every proof body is `sorry`; this file is a scaffold for sorry-driven development
(fill one stub at a time, `lake build` after each).  Mathlib already provides
`IsIndepSet`, `IsClique`, `indepNum`, `cliqueNum`, `IsNClique`, `IsNIndepSet`,
`CliqueFree`, `IndepSetFree`, the whole Turán API (`turanGraph`, `IsTuranMaximal`,
`CliqueFree.card_edgeFinset_le`), `IsCompleteMultipartite`, `IsContained` (`⊑`), etc.
— those are referenced, not redefined.

The repo modules the outline reuses (`Matchings/Defs`, `EulerHamilton/Defs`,
`Connectivity/Defs`) do **not** exist as importable files, so the few definitions
they carry (`IsCovering`, `IsVertexCut`, `join`, `degreeSequence`, `DegreeMajorised`)
are re-declared locally below — exactly as the Connectivity scaffold re-declares its
`IsVertexCut`/`vertexConnectivity` API.
-/

namespace SimpleGraph

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Re-declared repo definitions (the outline's `TCSlib.*` imports do not exist as files) -/

/-- A **covering** `K`: every edge has an end in `K`. (Repo `Matchings/Defs.lean:130`.)

## Book definition (§5.2, p. 81; recalled §7.1, p. 109) — verbatim

> Recall that a subset $K$ of $V$ such that every edge of $G$ has at least one end
> in $K$ is called a covering of $G$.

## In Lean notation

A set of vertices touching every edge.  Theorem 7.1 says coverings and
independent sets are exactly complementary.

⚠ Duplicated from `Matchings.lean`, textually identical.  Neither file imports the
other; see `log/graphtheory-ISSUES.md` §F.
-/
def IsCovering {V : Type*} (G : SimpleGraph V) (K : Set V) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → u ∈ K ∨ v ∈ K

/-- A **vertex cut** `S` (a *cut vertex* is the singleton case `S = {v}`).
(Repo `Connectivity/Defs.lean:42`.)

## Book definition (§3.1, p. 50) — verbatim

> A *vertex cut* of $G$ is a subset $V'$ of $V$ such that $G - V'$ is
> disconnected.

## In Lean notation

A *cut vertex* is the singleton case `S = {v}`, which is all this chapter needs.

⚠ The **fifth** independent copy of this definition in the directory
(`Connectivity`, `EulerHamilton`, `VertexColourings`, `PlanarGraphs`, here).

## Where it is used

Exercises 7.1.2 and 7.1.3(a) only.
-/
def IsVertexCut {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  (↑S : Set V) ⊂ Set.univ ∧ ¬ (G.induce ((↑S : Set V)ᶜ)).Connected

/-- The **join** `G ∨ H`. (Repo `EulerHamilton/Defs.lean:72`.)

## Book definition (§4.2, p. 66) — verbatim

> The *join* $G \vee H$ of disjoint graphs $G$ and $H$ is the graph obtained from
> $G + H$ by joining each vertex of $G$ to each vertex of $H$.

## In Lean notation

`(G ⊕g H) ⊔ completeBipartiteGraph V W` on carrier `V ⊕ W` — identical to
`EulerHamilton.lean`'s `join`, and duplicated for the same import reason.

## Where it is used

The central construction in Theorem 7.8: a `K_{n+1}`-free graph is analysed by
splitting off `N(u)` for a maximum-degree `u` and rebuilding as `G₁ ∨ G₂`.
-/
def join {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) :=
  (G ⊕g H) ⊔ completeBipartiteGraph V W

/-- The **degree sequence** of `G` as a `List ℕ`. (Repo `EulerHamilton/Defs.lean:82`.)
NOTE: the repo version is sorted descending; here we take the raw list of degrees, which is
sufficient for scaffolding (`DegreeMajorised` below is stated over it either way).

## Book definition (exercise 1.5.5)

Listing the vertices as `v₁, …, v_ν`, the sequence `(d(v₁), …, d(v_ν))` is a
degree sequence of `G`.  Chapter 7 uses it in Theorems 7.8 and 7.9, comparing a
`K_{m+1}`-free graph degree-by-degree with a complete multipartite graph.

## In Lean notation

⚠ **This version is UNSORTED** — `Finset.univ.toList.map degree`, in whatever
order `toList` produces.  `EulerHamilton.lean`'s version sorts *ascending*, and
the file header here claims the repo version sorts *descending*; all three
descriptions disagree.

That matters: `DegreeMajorised` below compares the two lists **entry by entry at
the same index**, which is only meaningful if both are sorted the same way.
Against an unsorted list the predicate depends on `Finset.univ.toList`'s
arbitrary order and is not isomorphism-invariant.

The docstring calls this "sufficient for scaffolding", which is true only in the
sense that it typechecks.  Any proof of Theorem 7.8 or 7.9 must sort first, or
restate `DegreeMajorised` over multisets.
-/
noncomputable def degreeSequence {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : List ℕ :=
  Finset.univ.toList.map (fun v => G.degree v)

/-- `G` is **degree-majorised** by `H`. (Repo `EulerHamilton/Defs.lean:139`.)

## Book definition (§4.2, p. 66) — verbatim

> A graph $G$ is *degree-majorised* by a graph $H$ if $\nu(G) = \nu(H)$ and the
> nondecreasing degree sequence of $G$ is majorised by that of $H$.

## In Lean notation

⚠ The book says **nondecreasing** degree sequence.  This file's `degreeSequence`
is unsorted (see the warning there), so the entrywise comparison here does not
implement the book's definition.  Fix `degreeSequence` before proving anything
that uses this.

## Where it is used

Theorem 7.8 — a degree-majorisation result exactly parallel to Theorem 4.6 for
hamiltonicity.  The book remarks on the similarity explicitly (§7.3, p. 118):

> It is interesting to note that the above theorem bears a striking similarity to
> theorem 4.6.
-/
def DegreeMajorised {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] : Prop :=
  Fintype.card V = Fintype.card W ∧
    ∀ i : ℕ, G.degreeSequence.getD i 0 ≤ H.degreeSequence.getD i 0

/-! # §7.1 — Independent Sets -/

-- Thm 7.1: `S` is an independent set iff `V \ S` (i.e. `Sᶜ`) is a covering.
/-- ## Book statement (§7.1, p. 109) — verbatim

> **Theorem 7.1** A set $S \subseteq V$ is an independent set of $G$ if and only
> if $V \backslash S$ is a covering of $G$.

## Book proof (§7.1, p. 109) — verbatim

> By definition, $S$ is an independent set of $G$ if and only if no edge of $G$
> has both ends in $S$ or, equivalently, if and only if each edge has at least one
> end in $V \backslash S$. But this is so if and only if $V \backslash S$ is a
> covering of $G$.

## In Lean notation

`V \ S` is `Sᶜ`.  Independent sets and coverings are complementary, which is why
the book's figure 7.1 shows independent sets visibly complementing coverings.

## Proof plan

Unfold both sides and push negations:
`G.IsIndepSet S` is `∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v`;
`G.IsCovering Sᶜ` is `∀ u v, G.Adj u v → u ∉ S ∨ v ∉ S`.
`constructor` plus `by_contra`/`push_neg` on each direction; `tauto` should close
both once the memberships are unfolded.

⚠ Mathlib's `IsIndepSet` carries a `u ≠ v` guard that the covering side does not;
`G.loopless` supplies it in the reverse direction.

## Status

`sorry`.  The easiest theorem in the chapter — genuinely a few lines, and worth
doing first since Corollary 7.1 depends on it.
-/
theorem isIndepSet_iff_isCovering_compl {V : Type*} (G : SimpleGraph V) (S : Set V) :
    G.IsIndepSet S ↔ G.IsCovering Sᶜ := by
  sorry

/-- The covering number `β(G)`. (NEEDED-TO-STATE; `IsCovering` is the repo predicate.)
No `Nat.sInf ∅ = 0` trap: `Set.univ` always covers, so the set is nonempty.

## Book definition (§7.1, p. 109) — verbatim

> The number of vertices in a maximum independent set of $G$ is called the
> *independence number* of $G$ and is denoted by $\alpha(G)$; similarly, the
> number of vertices in a minimum covering of $G$ is the *covering number* of $G$
> and is denoted by $\beta(G)$.

## In Lean notation

The fewest vertices touching every edge.  `α` is Mathlib's `indepNum`; only `β`
needs defining here.

✅ No `sInf ∅ = 0` pitfall: `Set.univ` is always a covering, so the set being
minimised is never empty.  Contrast `edgeCoveringNumber` below, where the trap is
live.
-/
noncomputable def coveringNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ K : Set V, G.IsCovering K ∧ K.ncard = n}

-- Cor 7.1: α + β = ν.
/-- ## Book statement (§7.1, p. 109) — verbatim

> **Corollary 7.1** $\alpha + \beta = \nu$.

## Book proof (§7.1, pp. 109–110) — verbatim

> Let $S$ be a maximum independent set of $G$, and let $K$ be a minimum covering
> of $G$. Then, by theorem 7.1, $V \backslash K$ is an independent set and
> $V \backslash S$ is a covering. Therefore
> $$\nu - \beta = |V \backslash K| \le \alpha \tag{7.1}$$
> and
> $$\nu - \alpha = |V \backslash S| \ge \beta \tag{7.2}$$
> Combining (7.1) and (7.2) we have $\alpha + \beta = \nu$.

## In Lean notation

The largest independent set and the smallest covering are exact complements:
choosing one is the same problem as choosing the other.

## Proof plan

1. Extremal witnesses exist — `V` finite, and both sets being optimised are
   nonempty (`∅` is independent, `univ` covers).  ⚠ `indepNum` is an `sSup` and
   `coveringNumber` an `sInf`; neither attainment is packaged, so both need
   `Nat.sSup_mem` / `Nat.sInf_mem` with an explicit boundedness argument.
2. (7.1): `Sᶜ` for `S` a minimum covering is independent by Thm 7.1, so
   `ν - β ≤ α`.
3. (7.2): `Sᶜ` for `S` a maximum independent set covers, so `β ≤ ν - α`.
4. `omega` — ⚠ but only after converting the ℕ subtractions; state both as
   `ν ≤ α + β` and `α + β ≤ ν` to stay additive.

## Status

`sorry`, depends on Thm 7.1.
-/
theorem indepNum_add_coveringNumber {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.indepNum + G.coveringNumber = Fintype.card V := by
  sorry

/-- The matching number `α′(G)`. (NEEDED-TO-STATE.)

## Book definition (§7.1, p. 110) — verbatim

> The edge analogue of an independent set is a set of links no two of which are
> adjacent, that is, a matching. [...] We denote the number of edges in a maximum
> matching of $G$ by $\alpha'(G)$ [...] the *edge independence number*.

## In Lean notation

An `sSup` over matching sizes — the edge analogue of `α`.  Bounded above by
`ε`, so the supremum is attained; as with `coveringNumber` that attainment is not
packaged and must be re-derived at each use.
-/
noncomputable def matchingNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sSup {n | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = n}

/-- An **edge covering** `L`: every vertex is an end of some edge of `L`. (NEEDED-TO-STATE.)

## Book definition (§7.1, p. 110) — verbatim

> The edge analogue of a covering is called an edge covering. An *edge covering*
> of $G$ is a subset $L$ of $E$ such that each vertex of $G$ is an end of some
> edge in $L$. Note that edge coverings do not always exist; a graph $G$ has an
> edge covering if and only if $\delta > 0$.

## In Lean notation

A set of edges touching every vertex.  The `L ⊆ G.edgeSet` conjunct is the book's
"subset of `E`", which matters here — without it `L` could contain non-edges and
cover trivially.

The existence caveat is what forces the `δ > 0` hypothesis on Theorem 7.2; see
`edgeCoveringNumber` below.
-/
def IsEdgeCovering {V : Type*} (G : SimpleGraph V) (L : Set (Sym2 V)) : Prop :=
  L ⊆ G.edgeSet ∧ ∀ v : V, ∃ e ∈ L, v ∈ e

/-- The edge covering number `β′(G)`. (NEEDED-TO-STATE.)
`Nat.sInf ∅ = 0` IS a live trap when `δ = 0` — hence the `δ > 0` hypothesis in Thm 7.2.

## Book definition (§7.1, p. 110) — verbatim

> [We denote] the number of edges in a minimum edge covering of $G$ by
> $\beta'(G)$; the numbers $\alpha'(G)$ and $\beta'(G)$ are the *edge
> independence number* and *edge covering number* of $G$, respectively.

## In Lean notation

The fewest edges touching every vertex.

⚠ **`sInf ∅ = 0` is a live trap here**, unlike `coveringNumber`.  When `δ = 0` no
edge covering exists, the set being minimised is empty, and Lean's convention
silently returns `0` — a value the book would call undefined.  That is precisely
why Theorem 7.2 carries `δ > 0`, and why any lemma about `β'` must either assume
it or handle the degenerate case explicitly.
-/
noncomputable def edgeCoveringNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ L : Set (Sym2 V), G.IsEdgeCovering L ∧ L.ncard = n}

-- Thm 7.2 (Gallai, 1959): if δ > 0 then α′ + β′ = ν.
/-- ## Book statement (§7.1, p. 110) — verbatim

> **Theorem 7.2** (Gallai, 1959)   If $\delta > 0$, then $\alpha' + \beta' = \nu$.

## Book proof (§7.1, p. 110) — verbatim

> Let $M$ be a maximum matching in $G$ and let $U$ be the set of $M$-unsaturated
> vertices. Since $\delta > 0$ and $M$ is maximum, there exists a set $E'$ of
> $|U|$ edges, one incident with each vertex in $U$. Clearly, $M \cup E'$ is an
> edge covering of $G$, and so
> $$\beta' \le |M \cup E'| = \alpha' + (\nu - 2\alpha') = \nu - \alpha'$$
> or
> $$\alpha' + \beta' \le \nu \tag{7.3}$$
> Now let $L$ be a minimum edge covering of $G$, set $H = G[L]$ and let $M$ be a
> maximum matching in $H$. Denote the set of $M$-unsaturated vertices in $H$ by
> $U$. Since $M$ is maximum, $H[U]$ has no links and therefore
> $$|L| - |M| = |L \backslash M| \ge |U| = \nu - 2|M|$$
> Because $H$ is a subgraph of $G$, $M$ is a matching in $G$ and so
> $$\alpha' + \beta' \ge |M| + |L| \ge \nu \tag{7.4}$$
> Combining (7.3) and (7.4), we have $\alpha' + \beta' = \nu$.

## In Lean notation

The striking parallel with Corollary 7.1 — even though matchings and edge
coverings are **not** complementary the way independent sets and coverings are.
The book is explicit about this (§7.1, p. 110):

> Matchings and edge coverings are not related to one another as simply as are
> independent sets and coverings; the complement of a matching need not be an edge
> covering, nor is the complement of an edge covering necessarily a matching.

## Proof plan

(≤) 1. Take `M` maximum; `|U| = ν - 2α'` since `M` saturates `2α'` vertices.
    2. `δ > 0` lets one pick an incident edge per `u ∈ U` (a choice function).
    3. `M ∪ E'` covers, so `β' ≤ α' + (ν - 2α')`.

(≥) 4. Take `L` minimum, `H = G[L]`, `M` maximum in `H`.
    5. `H[U]` edgeless by maximality of `M` — an edge there would extend `M`.
    6. Each `u ∈ U` needs its own `L`-edge, and those are distinct from `M`'s, so
       `|L| - |M| ≥ |U|`.
    7. Chain to `α' + β' ≥ ν`.

⚠ Steps 3 and 6 both do ℕ subtraction on quantities that could underflow; state
everything additively (`2α' + |U| = ν`, `|M| + |U| ≤ |L|`) and let `omega` close.

⚠ Step 6's "those are distinct from `M`'s" is the one real content step and is
where `L` being *minimum* is used.

## Status

`sorry`.  Self-contained — no dependency on chapter 5's blocked machinery, which
makes it more approachable than Theorem 7.3 below.
-/
theorem matchingNumber_add_edgeCoveringNumber
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hδ : 0 < G.minDegree) :
    G.matchingNumber + G.edgeCoveringNumber = Fintype.card V := by
  sorry

-- Thm 7.3 (BLOCKED on König): in a bipartite graph with δ > 0, α = β′.
/-- ## Book statement (§7.1, p. 111) — verbatim

> **Theorem 7.3** In a bipartite graph $G$ with $\delta > 0$, the number of
> vertices in a maximum independent set is equal to the number of edges in a
> minimum edge covering.

## Book proof (§7.1, p. 111) — verbatim

> Let $G$ be a bipartite graph with $\delta > 0$. By corollary 7.1 and theorem
> 7.2, we have
> $$\alpha + \beta = \alpha' + \beta'$$
> and, since $G$ is bipartite, it follows from theorem 5.3 that $\alpha' = \beta$.
> Thus $\alpha = \beta'$.

## In Lean notation

König's min-max equality transported across the two Gallai identities.  The book
introduces it with (§7.1, p. 110):

> We can now prove a theorem that bears a striking formal resemblance to König's
> theorem (5.3).

## Proof plan

1. `indepNum_add_coveringNumber` gives `α + β = ν`.
2. `matchingNumber_add_edgeCoveringNumber` gives `α' + β' = ν` (uses `hδ`).
3. König gives `α' = β` for bipartite `G`.
4. `omega`.

⚠ Step 3 needs `Matchings.lean`'s `konig_matching_covering`, which is **`sorry`
and in a file this one does not import**.  Worse, that theorem is stated with
*both* extremal objects as hypotheses (`IsMaximumMatching`, `IsMinimumCovering`)
rather than in terms of `matchingNumber`/`coveringNumber`, so even once proved it
needs a bridge to the numeric form used here.

## Status

`sorry`, blocked on König.  Steps 1–2 and 4 are mechanical once Cor 7.1 and Thm
7.2 land, so this becomes a four-line proof the moment step 3 is available.
-/
theorem indepNum_eq_edgeCoveringNumber
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {X Y : Set V} (hbip : G.IsBipartiteWith X Y) (hδ : 0 < G.minDegree) :
    G.indepNum = G.edgeCoveringNumber := by
  sorry

-- Ex 7.1.1(a): G bipartite ↔ ν(H) ≤ 2·α(H) for every subgraph H.
/-- ## Book statement (§7.1, p. 111) — verbatim

> 7.1.1 &nbsp; (a) Show that $G$ is bipartite if and only if
> $\alpha(H) \geq \frac{1}{2}\nu(H)$ for every subgraph $H$ of $G$.

An exercise, so the book gives no proof.

## In Lean notation

(⇒) Every subgraph of a bipartite graph is bipartite, and the larger side of a
bipartition is an independent set with at least half the vertices.

(⇐) If `G` were not bipartite it would contain an odd cycle (Thm 1.2).  That
cycle on `2k+1` vertices has `α = k`, and `2k < 2k+1`, so the condition fails at
that subgraph.

Stated as `ν(H) ≤ 2·α(H)` to avoid division.

"Subgraph `H` of `G`" is `H : G.Subgraph`, which carries its own `verts` — so
`ν(H)` genuinely shrinks and the odd-cycle witness is expressible.  `H.coe` is
the subgraph viewed as a `SimpleGraph ↥H.verts`, and `H.verts.ncard` is used in
place of `Fintype.card ↥H.verts` to avoid an instance that `[Fintype V]` alone
does not supply.

## Proof plan

(⇒) From a 2-colouring of `G`, restrict to `H.verts`; the larger colour class is
independent in `H.coe` and has `≥ ν(H)/2` vertices, i.e. `ν(H) ≤ 2·α(H)`.

(⇐) Contrapositive.  `G` not bipartite ⇒ an odd cycle `C` of length `2k+1`
(`isBipartite_iff_no_odd_cycle`-style).  Build `H : G.Subgraph` with
`verts = C.support.toFinset` and `Adj` the cycle's edges; then `α(H) = k` while
`ν(H) = 2k+1`, so `2k+1 ≤ 2k` is false.

⚠ The `α(C_{2k+1}) = k` computation is the real work — it needs an argument that
no independent set in an odd cycle exceeds `k`, which is a pigeonhole along the
cycle and is not in Mathlib.

## Status

`sorry`.
-/
theorem isBipartite_iff_forall_subgraph_two_mul_indepNum_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    -- NOTE: outline wrote `Fintype.card H.verts`; using `H.verts.ncard` avoids requiring a
    -- `Fintype ↥H.verts` instance (not synthesizable from `[Fintype V]` alone).
    G.IsBipartite ↔ ∀ H : G.Subgraph, H.verts.ncard ≤ 2 * H.coe.indepNum := by
  sorry

-- Ex 7.1.1(b) (BLOCKED on König): G bipartite ↔ α(H) = β′(H) for every subgraph H with δ(H) > 0.
/-- ## Book statement (§7.1, p. 111) — verbatim

> (b) Show that $G$ is bipartite if and only if $\alpha(H) = \beta'(H)$ for every
> subgraph $H$ of $G$ such that $\delta(H) > 0$.

An exercise, so the book gives no proof.

## In Lean notation

(⇒) Theorem 7.3 applied subgraph-wise, every subgraph of a bipartite graph being
bipartite.

(⇐) Contrapositive: an odd cycle `H` on `2k+1` vertices has `δ(H) = 2 > 0`,
`α(H) = k` and `β'(H) = k + 1`, so the equality fails there.

So the identity `α = β'` — which Theorem 7.3 gives for bipartite graphs —
actually *characterises* them.

⚠ The instance binders `[Fintype H.verts] → [DecidableRel H.coe.Adj] →` sit
**inside** the `∀ H`, as hypotheses rather than instance arguments.  That is
unusual and means a user must supply them explicitly at each application; it also
means the (⇐) direction gets to *assume* them for its witness, which is harmless
here but worth noticing.

## Proof plan

1. (⇒) restrict the bipartition to `H.verts` and apply
   `indepNum_eq_edgeCoveringNumber`.
2. (⇐) build the odd-cycle subgraph as in part (a), then compute both
   parameters: `α = k` (the same pigeonhole part (a) needs) and `β' = k + 1`
   (a cycle on `2k+1` vertices needs `⌈(2k+1)/2⌉` edges to cover).

## Status

`sorry`, blocked on Theorem 7.3 and hence on König.
-/
theorem isBipartite_iff_forall_subgraph_indepNum_eq_edgeCoveringNumber
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsBipartite ↔
      ∀ H : G.Subgraph, [Fintype H.verts] → [DecidableRel H.coe.Adj] → 0 < H.coe.minDegree →
        H.coe.indepNum = H.coe.edgeCoveringNumber := by
  sorry

/-- α-critical: deleting any edge raises the independence number. (NEEDED-TO-STATE; static.)

## Book definition (exercise 7.1.2, p. 111) — verbatim

> 7.1.2 &nbsp; A graph is $\alpha$-*critical* if $\alpha(G - e) > \alpha(G)$ for
> all $e \in E$.

## In Lean notation

Every edge matters for `α`: removing any one lets a larger independent set
appear, so an `α`-critical graph has no `α`-redundant edges.

`G - e` is `G.deleteEdges {e}`, on the same vertex type — so `ν` is unchanged,
which is what makes the equivalence with `β`-criticality (below) exact.
-/
def IsAlphaCritical {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ e ∈ G.edgeSet, G.indepNum < (G.deleteEdges {e}).indepNum

-- Ex 7.1.2: a connected α-critical graph has no cut vertices.
/-- ## Book statement (§7.1, p. 111) — verbatim

> 7.1.2 &nbsp; A graph is $\alpha$-*critical* if $\alpha(G - e) > \alpha(G)$ for
> all $e \in E$. Show that a connected $\alpha$-critical graph has no cut
> vertices.

An exercise, so the book gives no proof.

## In Lean notation

Suppose `v` is a cut vertex, so `G - v` splits.  Independent sets can be chosen
per component, and one shows some edge at `v` is deletable without increasing
`α` — contradicting criticality, where *every* deletion must raise it.

So `α`-criticality forces a structure that cannot be pieced together at a single
articulation point.

## Proof plan

1. Suppose `{v}` is a vertex cut; take two components `A`, `B` of `G - v`.
2. Build a maximum independent set `S` of `G`.  Split on whether `v ∈ S`:
   * `v ∈ S`: then `S` meets no neighbour of `v`, and deleting any edge at `v`
     leaves `S` still maximum — contradicting criticality at that edge.
   * `v ∉ S`: then `S ∩ A` and `S ∩ B` are independent in their components and
     `S` extends into one side; an exchange argument produces an edge whose
     deletion does not raise `α`.
3. Either way contradicts `hcrit`.

⚠ Step 2's exchange argument is the content and the book gives no hint.  The
standard route uses that `α(G) = α(G[A ∪ {v}]) + α(G[B])` when `v` separates —
an additivity lemma that is not in the file.

## Status

`sorry`.
-/
theorem no_cutVertex_of_isAlphaCritical
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hconn : G.Connected) (hcrit : G.IsAlphaCritical) (v : V) :
    ¬ G.IsVertexCut {v} := by
  sorry

/-- β-critical: deleting any edge lowers the covering number. (NEEDED-TO-STATE; static.)

## Book definition (exercise 7.1.3, p. 111) — verbatim

> 7.1.3 &nbsp; A graph $G$ is $\beta$-*critical* if $\beta(G - e) < \beta(G)$ for
> all $e \in E$.

## In Lean notation

Every edge is essential to the covering number.

✅ By Corollary 7.1 (`α + β = ν`) and the fact that edge deletion leaves `ν`
unchanged, this is **literally equivalent** to `IsAlphaCritical` — which is why
the two exercises are parallel, and why 7.1.3(a) reduces to 7.1.2 in one line
once Cor 7.1 is available.
-/
def IsBetaCritical {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).coveringNumber < G.coveringNumber

-- Ex 7.1.3(a): a connected β-critical graph has no cut vertices.
/-- ## Book statement (§7.1, p. 111) — verbatim

> 7.1.3 &nbsp; A graph $G$ is $\beta$-*critical* if $\beta(G - e) < \beta(G)$ for
> all $e \in E$. Show that
> &nbsp;(a) a connected $\beta$-critical graph has no cut vertices;

An exercise, so the book gives no proof.

## In Lean notation

Corollary 7.1 gives `α + β = ν` for every graph on the vertex type, and edge
deletion leaves `ν` fixed.  So `β(G - e) < β(G)` ⟺ `α(G - e) > α(G)`, and
`β`-critical is the same condition as `α`-critical.

## Proof plan

1. Prove `IsBetaCritical G ↔ IsAlphaCritical G` from `indepNum_add_coveringNumber`
   applied to both `G` and `G.deleteEdges {e}` — the two `ν`s agree, so `omega`.
2. `exact no_cutVertex_of_isAlphaCritical hconn (step1.mp hcrit) v`.

Worth stating step 1 as its own lemma; it is the whole content and is reusable.

## Status

`sorry`, reduces to Ex 7.1.2 once Cor 7.1 lands.
-/
theorem no_cutVertex_of_isBetaCritical
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hconn : G.Connected) (hcrit : G.IsBetaCritical) (v : V) :
    ¬ G.IsVertexCut {v} := by
  sorry

-- Ex 7.1.3(b)*: if G is connected then 2β ≤ ε + 1.
/-- ## Book statement (§7.1, p. 111) — verbatim

> &nbsp;(b)* if $G$ is connected, then $\beta \leq \frac{1}{2}(\varepsilon + 1)$.

A starred exercise, so the book gives no proof.

## In Lean notation

Stated as `2β ≤ ε + 1` to avoid division.

A minimum covering touches every edge, and in a connected graph the edges are
linked tightly enough that each covering vertex can be charged at least two
edges, with one left over for a spanning tree's root.

⚠ Note the book states this under 7.1.3, whose preamble defines `β`-critical —
but part (b) does **not** assume `β`-criticality, only connectivity, and the Lean
signature correctly reflects that.  (The docstring previously implied the
`β`-critical hypothesis carried over; it does not.)

Connectivity is essential: a disjoint union of `k` edges has `β = k = ε`, which
violates the bound for `k ≥ 2`.

## Proof plan

1. Take a spanning tree `T` (`Trees.lean`'s `exists_spanningTree`), so
   `ε(T) = ν - 1 ≤ ε`.
2. A minimum covering of `G` is in particular a covering of `T`.
3. For a tree, `2β(T) ≤ ε(T) + 1` by induction on leaves — each leaf's edge can
   be covered by its non-leaf end, charging two edges per covering vertex.
4. Conclude via `β(G) ≤ β(T)`? ⚠ **This direction is wrong** — `G` has more
   edges than `T`, so `β(G) ≥ β(T)`, and step 4 does not follow.  The tree route
   bounds the wrong side; a correct proof charges covering vertices to edges of
   `G` directly, using connectivity to rule out isolated-edge configurations.

## Status

`sorry`.  The plan above is incomplete at step 4 — flagged rather than papered
over.
-/
theorem two_mul_coveringNumber_le
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) :
    2 * G.coveringNumber ≤ #G.edgeFinset + 1 := by
  sorry

/-! # §7.2 — Ramsey's Theorem -/

/-- `IsRamseyBound n k l`: every graph on `n` vertices has a `k`-clique or an `l`-indep set.
(NEEDED-TO-STATE; static.)

## Book context (§7.2, p. 111) — verbatim

> In this section we deal only with simple graphs. A *clique* of a simple graph
> $G$ is a subset $S$ of $V$ such that $G[S]$ is complete. Clearly, $S$ is a
> clique of $G$ if and only if $S$ is an independent set of $G^c$, and so the two
> concepts are complementary.

> If $G$ has no large cliques, then one might expect $G$ to have a large
> independent set. That this is indeed the case was first proved by Ramsey (1930).
> He showed that, given any positive integers $k$ and $l$, there exists a smallest
> integer $r(k, l)$ such that every graph on $r(k, l)$ vertices contains either a
> clique of $k$ vertices or an independent set of $l$ vertices.

## In Lean notation

`IsRamseyBound n k l` says `n` is already large enough for that conclusion:
`∀ G : SimpleGraph (Fin n), (∃ s, G.IsNClique k s) ∨ (∃ t, G.IsNIndepSet l t)`.

Fixing the carrier as `Fin n` rather than quantifying over all `n`-element types
is what makes `ramseyNumber` an `sInf` over `ℕ` below.

Total disorder is impossible: any sufficiently large graph contains one kind of
order or the other.
-/
def IsRamseyBound (n k l : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), (∃ s, G.IsNClique k s) ∨ (∃ t, G.IsNIndepSet l t)

/-- The Ramsey number `r(k, l)`. (NEEDED-TO-STATE.)
`Nat.sInf ∅ = 0` is a live trap until `exists_isRamseyBound` is proved.

## Book definition (§7.2, p. 112) — verbatim

> The numbers $r(k, l)$ are known as the *Ramsey numbers*.

with the defining property quoted on `IsRamseyBound` above.

## In Lean notation

The exact threshold at which order becomes unavoidable.

⚠ **`sInf ∅ = 0` is a live trap** until `exists_isRamseyBound` is proved: without
it every `ramseyNumber k l` could silently be `0`, and every theorem below would
be about the wrong number.  That existence result is therefore not optional
scaffolding — it gates the meaning of the definition itself.

## Book table (§7.2, p. 114) — verbatim

> The following table shows all Ramsey numbers $r(k, l)$ known to date.
>
> | $k \backslash l$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
> |---|---|---|---|---|---|---|---|
> | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
> | 2 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
> | 3 | 1 | 3 | 6 | 9 | 14 | 18 | 23 |
> | 4 | 1 | 4 | 9 | 18 | | | |

> The determination of the Ramsey numbers in general is a very difficult unsolved
> problem.

(Still true; `r(5,5)` remains unknown.)
-/
noncomputable def ramseyNumber (k l : ℕ) : ℕ :=
  sInf {n | SimpleGraph.IsRamseyBound n k l}

-- Extracted (isRamseyBound_mono): upward-closure of the Ramsey bound.
/-- ## Book context

Not stated in the book — extracted here because the phrase "the *smallest*
integer `r(k, l)` such that…" presupposes the set of valid bounds is
upward-closed, and Lean needs that spelled out.

## In Lean notation

A bigger graph contains a smaller one: restrict a graph on `m` vertices to any
`n` of them, get a `k`-clique or `l`-independent set there, and it survives in
the larger graph.

## Proof plan

1. Given `G : SimpleGraph (Fin m)`, take the embedding `Fin n ↪ Fin m` from
   `hnm` (`Fin.castLEEmb`).
2. Pull `G` back along it (`SimpleGraph.comap`) to a graph on `Fin n`.
3. Apply `h`; a clique/indep set of the pullback maps forward to one of `G` under
   the embedding, since `comap` preserves both in the required direction.

⚠ Step 3 needs `IsNClique`/`IsNIndepSet` to transport along an *injection*, with
the cardinality preserved — `Finset.card_image_of_injective` plus the adjacency
correspondence.  Straightforward but not a one-liner.

## Status

`sorry`.
-/
theorem isRamseyBound_mono {n m k l : ℕ} (hnm : n ≤ m) (h : SimpleGraph.IsRamseyBound n k l) :
    SimpleGraph.IsRamseyBound m k l := by
  sorry

-- Extracted (Ramsey existence — B&M *cites*, never proves; gates all of §7.2 and §7.4).
/-- ## Book context (§7.2, p. 111) — verbatim

> He showed that, given any positive integers $k$ and $l$, there exists a smallest
> integer $r(k, l)$ such that every graph on $r(k, l)$ vertices contains either a
> clique of $k$ vertices or an independent set of $l$ vertices.

⚠ Bondy & Murty **cite** this and never prove it — Theorem 7.4 assumes the
numbers exist and bounds them.  So there is no book proof to quote, and this
lemma has to be established from scratch.

## In Lean notation

No matter how a graph is drawn, if it is large enough it cannot avoid *both* a
big clique and a big independent set.

## Why it matters more here than in the book

The book can be informal about existence because `r(k,l)` is only ever used
comparatively.  In Lean, `ramseyNumber` is `sInf` over a set that this lemma
proves nonempty — so **until this is proved, every `ramseyNumber` in the file is
provably `0`** and every result below is vacuous.  It gates all of §7.2 and, via
Schur, §7.4.

## Proof plan

Strong induction on `k + l`, mirroring Theorem 7.4's recursion:
1. Base: `k ≤ 1` or `l ≤ 1` — `n = 1` works, since a single vertex is a 1-clique
   and a 1-element independent set.
2. Step: given bounds `a` for `(k, l-1)` and `b` for `(k-1, l)`, show `a + b`
   bounds `(k, l)` — this is exactly `ramsey_recursion` below, so the two should
   be proved together, with this one consuming that.

⚠ Circularity hazard: `ramsey_recursion` is stated in terms of `ramseyNumber`,
which presupposes *this* lemma.  The induction must therefore be run at the level
of `IsRamseyBound` (as here), and `ramsey_recursion` derived afterwards — not the
other way round.

## Status

`sorry`.  ⭐ **The single most important stub in the chapter**: everything in
§7.2 and §7.4 is vacuous without it.
-/
theorem exists_isRamseyBound (k l : ℕ) : ∃ n, SimpleGraph.IsRamseyBound n k l := by
  sorry

/-- The consequence every later item consumes: `r(k,l)` really is a Ramsey bound.

## Book context

Implicit in the book's "the smallest integer `r(k, l)` such that…", which asserts
both that the minimum exists and that it has the property.

## In Lean notation

`ramseyNumber` is an `sInf`.  Once the set is nonempty (`exists_isRamseyBound`)
it contains its infimum (`Nat.sInf_mem`), so `r(k,l)` genuinely has the defining
property.

Note `isRamseyBound_mono` is not needed for *this* — `Nat.sInf_mem` alone
suffices — but it is what makes `r(k,l)` the sharp threshold rather than merely
*a* bound.

## Proof plan

`Nat.sInf_mem (exists_isRamseyBound k l)`, modulo unfolding `ramseyNumber`.  A
one-liner once existence lands.

## Status

`sorry`.  The bridge every concrete Ramsey computation below consumes.
-/
theorem isRamseyBound_ramseyNumber (k l : ℕ) :
    SimpleGraph.IsRamseyBound (SimpleGraph.ramseyNumber k l) k l := by
  sorry

-- (7.5): r(1,l) = r(k,1) = 1.
/-- ## Book statement (§7.2, pp. 111–112) — verbatim

> For example, it is easy to see that
> $$r(1, l) = r(k, 1) = 1 \tag{7.5}$$

The book gives no proof ("it is easy to see").

## In Lean notation

A 1-clique is a single vertex, which any nonempty graph has.  So one vertex
suffices.

⚠ `n = 1` must genuinely satisfy `IsRamseyBound 1 1 l` **and** no smaller `n`
must — but `n = 0` also satisfies it vacuously *only if* `Fin 0` graphs have a
1-clique, which they do not.  So the `sInf` really is `1`, but the `n = 0` case
has to be ruled out explicitly rather than assumed.

## Proof plan

1. `IsRamseyBound 1 1 l`: for `G : SimpleGraph (Fin 1)`, `{0}` is a 1-clique.
2. `¬ IsRamseyBound 0 1 l`: on `Fin 0` there is no 1-element subset at all, so
   neither disjunct holds — hence `0` is not in the set.
3. `Nat.sInf` of a set containing `1` but not `0` is `1`.

`hl : 1 ≤ l` is not used by step 1 and appears unnecessary; harmless.

## Status

`sorry`.  Reachable directly — does not need `exists_isRamseyBound`, since step 1
exhibits a witness.
-/
theorem ramseyNumber_one_left (l : ℕ) (hl : 1 ≤ l) : SimpleGraph.ramseyNumber 1 l = 1 := by
  sorry

/-- ## Book statement (§7.2, pp. 111–112) — verbatim

> $$r(1, l) = r(k, 1) = 1 \tag{7.5}$$

## In Lean notation

A 1-element independent set is a single vertex.  The mirror image of
`ramseyNumber_one_left`, and derivable from it via `ramseyNumber_comm`
(Ex 7.2.1) — though proving it directly is just as short.

## Proof plan

As for `ramseyNumber_one_left`, with the second disjunct in place of the first.

## Status

`sorry`.
-/
theorem ramseyNumber_one_right (k : ℕ) (hk : 1 ≤ k) : SimpleGraph.ramseyNumber k 1 = 1 := by
  sorry

-- (7.6): r(2,l) = l, r(k,2) = k.
/-- ## Book statement (§7.2, p. 112) — verbatim

> $$r(2, l) = l, \qquad r(k, 2) = k \tag{7.6}$$

The book gives no proof.

## In Lean notation

A 2-clique is an edge.  On `l` vertices either some edge is present — a
2-clique — or there are none, and all `l` vertices are independent.  So `l`
suffices; and `l - 1` does not, since `⊥` on `Fin (l-1)` has no edge and no
`l`-element independent set.

## Proof plan

1. `IsRamseyBound l 2 l`: given `G`, case on whether `G.edgeSet` is empty.
   Nonempty ⇒ its endpoints are a 2-clique.  Empty ⇒ `Finset.univ` is an
   `l`-element independent set (needs `Fintype.card (Fin l) = l`).
2. `¬ IsRamseyBound (l-1) 2 l`: take `⊥ : SimpleGraph (Fin (l-1))`; no 2-clique
   (no edges) and no `l`-element independent set (only `l-1` vertices).
3. Combine with `isRamseyBound_mono` to get the `sInf` exactly `l`.

⚠ Step 2 needs `l ≥ 1` for `l - 1` not to underflow — that is what `hl` is for.

## Status

`sorry`.  Like (7.5), reachable without `exists_isRamseyBound`.
-/
theorem ramseyNumber_two_left (l : ℕ) (hl : 1 ≤ l) : SimpleGraph.ramseyNumber 2 l = l := by
  sorry

/-- ## Book statement (§7.2, p. 112) — verbatim

> $$r(2, l) = l, \qquad r(k, 2) = k \tag{7.6}$$

## In Lean notation

A 2-element independent set is a non-adjacent pair.  On `k` vertices either some
pair is non-adjacent, or every pair is adjacent and all `k` form a clique.  The
complete graph on `k - 1` vertices shows `k` is needed.

The mirror of `ramseyNumber_two_left` under `ramseyNumber_comm`.

## Proof plan

As for `ramseyNumber_two_left`, with `⊤` in place of `⊥` as the lower-bound
witness.

## Status

`sorry`.
-/
theorem ramseyNumber_two_right (k : ℕ) (hk : 1 ≤ k) : SimpleGraph.ramseyNumber k 2 = k := by
  sorry

-- Thm 7.4 (Erdős–Szekeres): r(k,l) ≤ r(k,l-1) + r(k-1,l).
/-- ## Book statement (§7.2, p. 112) — verbatim

> **Theorem 7.4** For any two integers $k \geq 2$ and $l \geq 2$
> $$r(k, l) \leq r(k, l-1) + r(k-1, l) \tag{7.7}$$
> Furthermore, if $r(k, l-1)$ and $r(k-1, l)$ are both even, then strict
> inequality holds in (7.7).

## Book proof (§7.2, p. 112) — verbatim, the inequality

> Let $G$ be a graph on $r(k, l-1) + r(k-1, l)$ vertices, and let $v \in V$. We
> distinguish two cases:
>
> (i) $v$ is nonadjacent to a set $S$ of at least $r(k, l-1)$ vertices, or
> (ii) $v$ is adjacent to a set $T$ of at least $r(k-1, l)$ vertices.
>
> Note that either case (i) or case (ii) must hold because the number of vertices
> to which $v$ is nonadjacent plus the number of vertices to which $v$ is adjacent
> is equal to $r(k, l-1) + r(k-1, l) - 1$.
>
> In case (i), $G[S]$ contains either a clique of $k$ vertices or an independent
> set of $l-1$ vertices, and therefore $G[S \cup \{v\}]$ contains either a clique
> of $k$ vertices or an independent set of $l$ vertices. Similarly, in case (ii),
> $G[T \cup \{v\}]$ contains either a clique of $k$ vertices or an independent set
> of $l$ vertices. Since one of case (i) and case (ii) must hold, it follows that
> $G$ contains either a clique of $k$ vertices or an independent set of $l$
> vertices. This proves (7.7).

## In Lean notation

The engine behind both the exact values in the book's table and the binomial
bound of Theorem 7.5.

⚠ `l - 1` and `k - 1` are ℕ subtraction; `hk`, `hl` keep them from truncating,
but the proof must still convert `l - 1 + 1 = l` explicitly at each use.

## Proof plan

1. Show `IsRamseyBound (r(k,l-1) + r(k-1,l)) k l`, then `Nat.sInf_le`.
2. Fix `G` and `v`.  Partition `Fin n \ {v}` into neighbours and non-neighbours;
   their sizes sum to `n - 1`, so pigeonhole gives (i) or (ii).
3. Case (i): restrict to `S`, apply `isRamseyBound_ramseyNumber k (l-1)` via
   `isRamseyBound_mono`; a `k`-clique transfers, an `(l-1)`-indep set plus `v`
   (non-adjacent to all of `S`) is an `l`-indep set.
4. Case (ii): symmetric, with `v` adjacent to all of `T`.

⚠ Steps 3–4 need clique/indep-set transport along the inclusion `S ↪ Fin n`, the
same transport `isRamseyBound_mono` needs — worth factoring out once.

⚠ The `insert v` steps need `v ∉ S` and the adjacency/non-adjacency to *every*
element of `S`, which is how `S` was chosen; keep that as an explicit hypothesis
rather than re-deriving.

## Status

`sorry`, and depends on `isRamseyBound_ramseyNumber` (hence on
`exists_isRamseyBound`).  See the circularity note there: the induction should be
run at `IsRamseyBound` level first.
-/
theorem ramsey_recursion {k l : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ l) :
    SimpleGraph.ramseyNumber k l
      ≤ SimpleGraph.ramseyNumber k (l - 1) + SimpleGraph.ramseyNumber (k - 1) l := by
  sorry

-- Thm 7.4 (strict form when both summands are even).
/-- ## Book statement (§7.2, p. 112) — verbatim

> Furthermore, if $r(k, l-1)$ and $r(k-1, l)$ are both even, then strict
> inequality holds in (7.7).

## Book proof (§7.2, p. 112) — verbatim

> Now suppose that $r(k, l-1)$ and $r(k-1, l)$ are both even, and let $G$ be a
> graph on $r(k, l-1) + r(k-1, l) - 1$ vertices. Since $G$ has an odd number of
> vertices, it follows from corollary 1.1 that some vertex $v$ is of even degree;
> in particular, $v$ cannot be adjacent to precisely $r(k-1, l) - 1$ vertices.
> Consequently, either case (i) or case (ii) above holds, and therefore $G$
> contains either a clique of $k$ vertices or an independent set of $l$ vertices.
> Thus
> $$r(k, l) \leq r(k, l-1) + r(k-1, l) - 1$$
> as stated.

## In Lean notation

The parity refinement that pins down `r(3,4) = 9`: `r(3,3) = 6` and `r(2,4) = 4`
are both even, so `r(3,4) ≤ 6 + 4 - 1 = 9`.

⚠ The book's "in particular, `v` cannot be adjacent to precisely `r(k-1,l) - 1`
vertices" is the crux and compresses a parity computation: with both summands
even, `r(k-1,l) - 1` is odd, so a vertex of even degree cannot have exactly that
degree.  That one configuration is precisely the one where neither (i) nor (ii)
holds, so ruling it out restores the case analysis.

## Proof plan

1. As Theorem 7.4, but on `n = r(k,l-1) + r(k-1,l) - 1` vertices.
2. `n` is odd (sum of two evens, minus one), so
   `GraphsAndSubgraphs.lean`'s `even_card_odd_degree` gives a vertex `v` of even
   degree — ⚠ that lemma says the *count* of odd-degree vertices is even; getting
   an even-degree vertex from it needs `n` odd plus a counting step, not a direct
   application.
3. `deg v ≠ r(k-1,l) - 1` by parity; hence (i) or (ii).
4. Finish as in Theorem 7.4.

## Status

`sorry`, depends on Theorem 7.4's machinery plus step 2's parity extraction.
-/
theorem ramsey_recursion_strict {k l : ℕ} (hk : 2 ≤ k) (hl : 2 ≤ l)
    (he₁ : Even (SimpleGraph.ramseyNumber k (l - 1)))
    (he₂ : Even (SimpleGraph.ramseyNumber (k - 1) l)) :
    SimpleGraph.ramseyNumber k l
      < SimpleGraph.ramseyNumber k (l - 1) + SimpleGraph.ramseyNumber (k - 1) l := by
  sorry

-- (7.8): r(3,3) ≥ 6, via the 5-cycle.
/-- **Book equation (7.8), first ingredient.**  *The 5-cycle contains no clique of
three vertices.*

## Book statement (§7.2, p. 112) — verbatim

> The 5-cycle (figure 7.2a) contains no clique of three vertices and no
> independent set of three vertices. It shows, therefore, that
> $$r(3, 3) \geq 6 \tag{7.8}$$

## In Lean notation

`C₅` has girth 5, so no triangle: each vertex has two neighbours and they are not
adjacent to each other.

## Proof plan

✅ **`decide` is viable here.**  `CliqueFree 3` on 5 vertices is `C(5,3) = 10`
triples.  The obstacle is instance rather than size: `SimpleGraph.cycleGraph 5`
needs a `DecidableRel .Adj` instance for `decide` to fire, and `CliqueFree` must
reduce to a decidable `Finset` quantification.  `decide` after
`simp [CliqueFree, isNClique_iff]` is the usual shape.

## Status

`sorry`.
-/
theorem cycleGraph_five_cliqueFree_three : (SimpleGraph.cycleGraph 5).CliqueFree 3 := by
  sorry

/-- **Book equation (7.8), second ingredient.**  *The 5-cycle contains no
independent set of three vertices.*

## Book statement (§7.2, p. 112) — verbatim

> The 5-cycle (figure 7.2a) contains no clique of three vertices and no
> independent set of three vertices.

## In Lean notation

Any three of five cyclic positions include two consecutive ones, hence adjacent.
So `α(C₅) = 2`.

`C₅` is self-complementary, which is what makes it work on both sides at once —
the book conjectures (§7.2, p. 114) that all `(k,k)`-Ramsey graphs are.

## Proof plan

`decide`, as for the clique version — same instance caveat.

## Status

`sorry`.
-/
theorem cycleGraph_five_indepSetFree_three : (SimpleGraph.cycleGraph 5).IndepSetFree 3 := by
  sorry

/-- **Book equation (7.8).**  *`r(3, 3) ≥ 6`.*

## Book statement (§7.2, pp. 112–113) — verbatim

> $$r(3, 3) \geq 6 \tag{7.8}$$

with the matching upper bound (§7.2, p. 113):

> Firstly, by (7.7) and (7.6)
> $$r(3, 3) \leq r(3, 2) + r(2, 3) = 6$$
> and therefore, using (7.8), we have $r(3, 3) = 6$.

## In Lean notation

`C₅` witnesses that five vertices do not force either structure, so the threshold
is `≥ 6`.  Combined with Thm 7.4 this is the exact value: among any six people,
three are mutual acquaintances or three mutual strangers.

⚠ Only the **lower** bound is stated here; the file does not state `r(3,3) = 6`.
Same for `r(3,5)` and `r(4,4)` below — all three exact values in the book's
worked examples are left unstated.

## Proof plan

`Nat.le_sInf`-style: show `¬ IsRamseyBound n 3 3` for every `n < 6` by exhibiting
`cycleGraph 5` restricted to `Fin n` — ⚠ actually only `n = 5` needs the
`C₅` witness; smaller `n` follow from `isRamseyBound_mono` contrapositively, so
the argument is "if `5` is not a bound then no `n ≤ 5` is".

## Status

`sorry`, depends on the two `cycleGraph 5` lemmas above.
-/
theorem six_le_ramseyNumber_three_three : 6 ≤ SimpleGraph.ramseyNumber 3 3 := by
  sorry

/-- The (3,5)-Ramsey graph: `ZMod 13`, adjacent iff the difference is a cubic residue.
(NEEDED-TO-STATE.) `{1,5,8,12}` is closed under negation, so `symm` is genuine.

## Book construction (§7.2, p. 114) — verbatim

> A $(k, l)$-*Ramsey graph* is a graph on $r(k, l) - 1$ vertices that contains
> neither a clique of $k$ vertices nor an independent set of $l$ vertices. [...]
> Ramsey graphs often seem to possess interesting structures. [...] We get the
> $(3, 5)$-Ramsey graph by regarding the thirteen vertices as elements of the
> field of integers modulo 13, and joining two vertices by an edge if their
> difference is a cubic residue of 13 (either 1, 5, 8 or 12).

## In Lean notation

A circulant on `ZMod 13`.  `{1, 5, 8, 12}` is closed under negation
(`-1 = 12`, `-5 = 8`), which is exactly what makes `symm` hold — so unlike most
`def`s in this repo, `symm` and `loopless` are **genuinely discharged**, by
`decide`.

✅ Fully defined, no `sorry` — one of the few complete constructions in the
directory.
-/
def cubicResidueGraph13 : SimpleGraph (ZMod 13) where
  Adj x y := x - y ∈ ({1, 5, 8, 12} : Finset (ZMod 13))
  symm := by unfold Symmetric; decide
  loopless := by unfold Irreflexive; decide

-- (7.10): r(3,5) ≥ 14, via the cubic-residue graph mod 13.
/-- **Book equation (7.10), first ingredient.**  *The cubic-residue graph mod 13
contains no clique of three vertices.*

## Book context (§7.2, p. 113) — verbatim

> Similarly, the graph of figure 7.2*c* shows that
> $$r(3, 5) \geq 14 \tag{7.10}$$

The book asserts the graph's properties from the figure; there is no proof to
quote.

## In Lean notation

A triangle needs three residues pairwise differing by an element of
`{1, 5, 8, 12}`; the arithmetic rules it out.  The graph is 4-regular and
triangle-free.

## Proof plan

✅ **`decide` should be viable**: `C(13,3) = 286` triples, each a `ZMod 13`
membership test.  `cubicResidueGraph13` is fully defined with decidable
adjacency, so unlike most stubs here nothing blocks it.

⚠ Feasibility depends on `CliqueFree` reducing to a decidable `Finset`
quantification; `simp [CliqueFree, isNClique_iff]` first, then `decide`.  If the
kernel struggles, `Finset.decide`-style explicit enumeration is the fallback.

## Status

`sorry`.  ⭐ Among the most tractable in the chapter — a genuine finite check
with all its inputs already defined.
-/
theorem cubicResidueGraph13_cliqueFree_three : cubicResidueGraph13.CliqueFree 3 := by
  sorry

/-- **Book equation (7.10), second ingredient.**  *The cubic-residue graph mod 13
contains no independent set of five vertices.*

## Book context (§7.2, p. 113)

Asserted from figure 7.2*c*; no proof given.

## In Lean notation

Five pairwise non-adjacent vertices would be five residues no two differing by an
element of `{1, 5, 8, 12}`.  With thirteen residues and four forbidden
differences, no such set exists.

## Proof plan

`decide` — `C(13,5) = 1287` subsets, larger than the clique check but still
small.  Same instance caveat.

## Status

`sorry`.  Together with the previous lemma this makes `cubicResidueGraph13` a
`(3,5)`-Ramsey graph.
-/
theorem cubicResidueGraph13_indepSetFree_five : cubicResidueGraph13.IndepSetFree 5 := by
  sorry

/-- **Book equation (7.10).**  *`r(3, 5) ≥ 14`.*

## Book statement (§7.2, pp. 113–114) — verbatim

> $$r(3, 5) \geq 14 \tag{7.10}$$

with the matching upper bound (§7.2, p. 114):

> Now we again apply (7.7) and (7.6) to obtain
> $$r(3, 5) \leq r(3, 4) + r(2, 5) = 14$$
> [...] which, together with (7.10) [...] yield $r(3, 5) = 14$.

## In Lean notation

Thirteen vertices do not suffice, so the threshold is `≥ 14`.

⚠ The book's upper bound chain routes through `r(3,4) = 9`, which itself needs
the **strict** form of Theorem 7.4 (`r(3,3)` and `r(2,4)` both even).  Neither
`r(3,4) = 9` nor its ingredients are stated in this file, so the exact value
`r(3,5) = 14` is not reachable from what is here even once everything is proved.

## Proof plan

As for `six_le_ramseyNumber_three_three`, with `cubicResidueGraph13` as the
witness at `n = 13`.

## Status

`sorry`, depends on the two `cubicResidueGraph13` lemmas.
-/
theorem fourteen_le_ramseyNumber_three_five : 14 ≤ SimpleGraph.ramseyNumber 3 5 := by
  sorry

/-- The (4,4)-Ramsey graph = the Paley graph of order 17. (NEEDED-TO-STATE.)

## Book construction (§7.2, p. 114) — verbatim

> the $(4, 4)$-Ramsey graph is obtained by regarding the vertices as elements of
> the field of integers modulo 17, and joining two vertices if their difference is
> a quadratic residue of 17 (either 1, 2, 4, 8, 9, 13, 15 or 16). It has been
> conjectured that the $(k, k)$-Ramsey graphs are always self-complementary (that
> is, isomorphic to their complements); this is true for $k = 2$, 3 and 4.

## In Lean notation

The **Paley graph** of order 17 — the canonical self-complementary, highly
symmetric graph.  `{1,2,4,8,9,13,15,16}` is closed under negation
(`-1 = 16`, `-2 = 15`, …), so `symm` holds.

✅ Fully defined, `symm`/`loopless` discharged by `decide` — no `sorry`.
-/
def paleyGraph17 : SimpleGraph (ZMod 17) where
  Adj x y := x - y ∈ ({1, 2, 4, 8, 9, 13, 15, 16} : Finset (ZMod 17))
  symm := by unfold Symmetric; decide
  loopless := by unfold Irreflexive; decide

-- (7.11): r(4,4) ≥ 18, via the Paley graph mod 17.
/-- **Book equation (7.11), first ingredient.**  *The Paley graph of order 17
contains no clique of four vertices.*

## Book context (§7.2, p. 113) — verbatim

> the graph of figure 7.2*d* yields
> $$r(4, 4) \geq 18 \tag{7.11}$$

Asserted from the figure; no proof given.

## In Lean notation

Four vertices pairwise differing by quadratic residues would be a `K₄`; the
arithmetic of `{1,2,4,8,9,13,15,16}` prevents it, so `ω = 3`.

## Proof plan

`decide` — `C(17,4) = 2380` quadruples, each a `ZMod 17` membership test.  Larger
than the `ZMod 13` checks but the same shape, and `paleyGraph17` is fully
defined.

⚠ This is the biggest of the four finite checks; if the kernel times out,
reducing via `Finset.filter` over an explicit vertex list is the fallback.

## Status

`sorry`.
-/
theorem paleyGraph17_cliqueFree_four : paleyGraph17.CliqueFree 4 := by
  sorry

/-- **Book equation (7.11), second ingredient.**  *The Paley graph of order 17
contains no independent set of four vertices.*

## Book context (§7.2, p. 113)

Asserted from figure 7.2*d*.

## In Lean notation

✅ **The slick route**: the Paley graph of order 17 is self-complementary (the
book notes this), so a 4-element independent set would be a `K₄` in the
complement, i.e. in an isomorphic copy — ruled out by the previous lemma.

⚠ But that route costs a self-complementarity proof (an explicit isomorphism
`x ↦ gx` for `g` a non-residue), which is more work than the direct check.

## Proof plan

`decide` directly, exactly as for the clique version — `C(17,4) = 2380` again.
Cheaper than proving self-complementarity, unless that isomorphism is wanted for
its own sake.

## Status

`sorry`.
-/
theorem paleyGraph17_indepSetFree_four : paleyGraph17.IndepSetFree 4 := by
  sorry

/-- **Book equation (7.11).**  *`r(4, 4) ≥ 18`.*

## Book statement (§7.2, pp. 113–114) — verbatim

> $$r(4, 4) \geq 18 \tag{7.11}$$

with the matching upper bound (§7.2, p. 114):

> $$r(4, 4) \leq r(4, 3) + r(3, 4) = 18$$
> which, together with [...] (7.11), respectively, yield [...] $r(4, 4) = 18$.

## In Lean notation

Seventeen vertices do not suffice, so the threshold is `≥ 18` — and with the
upper bound, exactly `18`, the largest value in the book's table.

⚠ As with `r(3,5)`, only the lower bound is stated here, and the upper bound
would need `r(3,4) = 9` — itself unstated and requiring the strict form of
Theorem 7.4.

## Proof plan

As for the other two lower bounds, with `paleyGraph17` as the `n = 17` witness.

## Status

`sorry`, depends on the two `paleyGraph17` lemmas.
-/
theorem eighteen_le_ramseyNumber_four_four : 18 ≤ SimpleGraph.ramseyNumber 4 4 := by
  sorry

-- Thm 7.5: r(k,l) ≤ C(k+l-2, k-1).
/-- **Theorem 7.5**: `r(k, l) ≤ C(k + l - 2, k - 1)`.

## Book statement (§7.2, p. 114) — verbatim

> **Theorem 7.5** $\quad r(k, l) \leq \binom{k + l - 2}{k - 1}$

## Book proof (§7.2, pp. 114–115) — verbatim

> By induction on $k + l$. Using (7.5) and (7.6) we see that the theorem holds
> when $k + l \leq 5$. Let $m$ and $n$ be positive integers, and assume that the
> theorem is valid for all positive integers $k$ and $l$ such that
> $5 \le k + l < m + n$. Then, by theorem 7.4 and the induction hypothesis
> $$r(m, n) \le r(m, n-1) + r(m-1, n)$$
> $$\le \binom{m+n-3}{m-1} + \binom{m+n-3}{m-2} = \binom{m+n-2}{m-1}$$
> Thus the theorem holds for all values of $k$ and $l$.

## In Lean notation

Theorem 7.4's recursion is exactly Pascal's rule, so the Ramsey numbers are
dominated by binomial coefficients.  Setting `k = l` gives roughly `r(k,k) ≤ 4^k`;
Theorem 7.6 gives `2^{k/2}` below, and closing that gap is still open.

⚠ Three ℕ subtractions in the statement (`k + l - 2`, `k - 1`, and `m - 2` in the
proof).  The Pascal step `C(m+n-3, m-1) + C(m+n-3, m-2) = C(m+n-2, m-1)` is
`Nat.choose_succ_succ` only after the indices are massaged into `succ` form —
budget for that.

## Proof plan

1. Strong induction on `k + l`.
2. Base `k + l ≤ 5`: the (7.5)/(7.6) values, i.e. the four `ramseyNumber_*`
   lemmas above.
3. Step: `ramsey_recursion` then the induction hypothesis twice, then Pascal.

## Status

`sorry`, depends on Theorem 7.4 and the base-case values.
-/
theorem ramseyNumber_le_choose {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    SimpleGraph.ramseyNumber k l ≤ (k + l - 2).choose (k - 1) := by
  sorry

-- (7.12): |𝒢ₙ| = 2^C(n,2). (NEEDED-TO-STATE lemma; the Fintype instance exists, the count does not.)
/-- ## Book statement (§7.2, p. 115) — verbatim

> Denote by $\mathcal{G}_n$ the set of simple graphs with vertex set
> $\{v_1, v_2, \ldots, v_n\}$ [...] Clearly
> $$|\mathcal{G}_n| = 2^{\binom{n}{2}} \tag{7.12}$$
> since each subset of the $\binom{n}{2}$ possible edges $v_i v_j$ determines a
> graph in $\mathcal{G}_n$.

## In Lean notation

A simple graph on a labelled vertex set is determined by which of the `C(n,2)`
possible edges are present.

⚠ Mathlib has a `Fintype (SimpleGraph (Fin n))` instance but **no cardinality
lemma**, so this genuinely has to be proved.  The route is an equiv
`SimpleGraph (Fin n) ≃ (Sym2 (Fin n) \ diagonal → Bool)`, or via
`Finset.powerset` on the non-diagonal `Sym2`s — the `Sym2` bookkeeping is the
work, not the arithmetic.

## Why it matters

The counting fact underlying Erdős' probabilistic proof of Theorem 7.6.

## Status

`sorry`.
-/
theorem card_simpleGraph_fin (n : ℕ) :
    Fintype.card (SimpleGraph (Fin n)) = 2 ^ (n.choose 2) := by
  sorry

-- Thm 7.6 (Erdős, probabilistic): 2^{k/2} ≤ r(k,k)  (a real exponent).
/-- ## Book statement (§7.2, p. 115) — verbatim

> **Theorem 7.6**   (Erdös, 1947) $r(k, k) \ge 2^{k/2}$

## Book proof (§7.2, p. 115) — verbatim

> Since $r(1, 1) = 1$ and $r(2, 2) = 2$, we may assume that $k \ge 3$. Denote by
> $\mathcal{G}_n$ the set of simple graphs with vertex set
> $\{v_1, v_2, \ldots, v_n\}$, and by $\mathcal{G}_n^k$ the set of those graphs in
> $\mathcal{G}_n$ that have a clique of $k$ vertices. [(7.12) omitted — see
> `card_simpleGraph_fin`.] Similarly, the number of graphs in $\mathcal{G}_n$
> having a particular set of $k$ vertices as a clique is
> $2^{\binom{n}{2} - \binom{k}{2}}$. Since there are $\binom{n}{k}$ distinct
> $k$-element subsets of $\{v_1, v_2, \ldots, v_n\}$, we have
> $$|\mathcal{G}_n^k| \le \binom{n}{k} 2^{\binom{n}{2} - \binom{k}{2}} \tag{7.13}$$
> By (7.12) and (7.13)
> $$\frac{|\mathcal{G}_n^k|}{|\mathcal{G}_n|} \le \binom{n}{k} 2^{-\binom{k}{2}} < \frac{n^k 2^{-\binom{k}{2}}}{k!} \tag{7.14}$$
> Suppose, now, that $n < 2^{k/2}$. From (7.14) it follows that
> $$\frac{|\mathcal{G}_n^k|}{|\mathcal{G}_n|} < \frac{2^{k^2/2} 2^{-\binom{k}{2}}}{k!} = \frac{2^{k/2}}{k!} < \tfrac{1}{2}$$
> Therefore, fewer than half of the graphs in $\mathcal{G}_n$ contain a clique of
> $k$ vertices. Also, because
> $\mathcal{G}_n = \{G \mid G^c \in \mathcal{G}_n\}$, fewer than half of the
> graphs in $\mathcal{G}_n$ contain an independent set of $k$ vertices. Hence some
> graph in $\mathcal{G}_n$ contains neither a clique of $k$ vertices nor an
> independent set of $k$ vertices. Because this holds for any $n < 2^{k/2}$, we
> have $r(k, k) \ge 2^{k/2}$.

## In Lean notation

The **probabilistic method**, which the book introduces as (§7.2, p. 115):

> essentially a crude counting argument. Although nonconstructive, it can often be
> applied to assert the existence of a graph with certain specified properties.

The exponent `k/2` is real, hence the `ℝ`-valued statement — the one place in
this chapter where `ℕ` will not do.

## Proof plan

1. `k ≤ 2` separately (`r(1,1) = 1`, `r(2,2) = 2`).
2. Counting in `ℕ`: `|𝒢ₙᵏ| ≤ C(n,k) · 2^(C(n,2) - C(k,2))`.  ⚠ The exponent
   subtraction needs `C(k,2) ≤ C(n,2)`, true only when `k ≤ n` — handle `k > n`
   as a separate trivial case.
3. Cast to `ℝ` and run the chain (7.14).  ⚠ `C(n,k) < n^k / k!` is *strict* and
   needs `k ≥ 1`; `2^{k/2}/k! < ½` needs `k ≥ 3`, which is what step 1 buys.
4. The complementation step needs the map `G ↦ Gᶜ` to be an involution on
   `SimpleGraph (Fin n)` — cheap, but it is what makes "fewer than half" apply on
   both sides simultaneously.
5. Conclude: the two "fewer than half" sets cannot cover `𝒢ₙ`, so a witness
   exists; hence `¬ IsRamseyBound n k k` for every `n < 2^{k/2}`.

⚠ Step 5 is where the argument becomes non-constructive, and where `Nat.sInf`'s
characterisation (`Nat.not_mem_of_lt_sInf` or similar) has to be brought in.

## Status

`sorry`.  ⭐ The most analytically involved result in the chapter — real-valued
estimates, factorials, and a counting argument over the space of all graphs.
-/
theorem ramsey_self_lower_bound {k : ℕ} (hk : 1 ≤ k) :
    ((2 : ℝ) ^ ((k : ℝ) / 2)) ≤ (SimpleGraph.ramseyNumber k k : ℝ) := by
  sorry

-- Cor 7.6: 2^{min(k,l)/2} ≤ r(k,l).
/-- ## Book statement (§7.2, p. 116) — verbatim

> *Corollary 7.6* If $m = \min\{k, l\}$, then $r(k, l) \geq 2^{m/2}$

The book gives no proof — it is immediate from Theorem 7.6 plus monotonicity.

## In Lean notation

Ramsey numbers are monotone in both arguments, so `r(k,l) ≥ r(m,m)` for
`m = min(k,l)`; then Theorem 7.6.

⚠ **Monotonicity of `ramseyNumber` in its arguments is not stated in this file.**
`isRamseyBound_mono` is monotonicity in `n`, a different thing.  The needed
lemma — `k ≤ k' → l ≤ l' → r(k,l) ≤ r(k',l')` — has to be added; it follows from
`IsRamseyBound n k' l' → IsRamseyBound n k l` (a bigger clique contains a
smaller one).

## Proof plan

1. Add the argument-monotonicity lemma above.
2. `r(k,l) ≥ r(m,m)` with `m = min k l`.
3. `ramsey_self_lower_bound` at `m`, then cast.

## Book remark (§7.2, p. 116) — verbatim

> All known lower bounds for $r(k, l)$ obtained by constructive arguments are much
> weaker than that given in corollary 7.6; the best is due to Abbott (1972), who
> shows that $r(2^n + 1, 2^n + 1) \geq 5^n + 1$ (exercise 7.2.4).

The probabilistic method still proves more than anyone can build — `abbott_lower_bound`
below is that constructive record.

## Status

`sorry`, depends on Theorem 7.6 and the missing monotonicity lemma.
-/
theorem ramseyNumber_ge_of_min {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ((2 : ℝ) ^ ((min k l : ℝ) / 2)) ≤ (SimpleGraph.ramseyNumber k l : ℝ) := by
  sorry

/-- An `m`-edge-colouring of `Kₙ`: a total function on unordered pairs.
(NEEDED-TO-STATE.) NOT `SimpleGraph.Coloring`, which colours vertices.

## Book context (§7.2, p. 116) — verbatim

> The Ramsey numbers $r(k, l)$ are sometimes defined in a slightly different way
> from that given at the beginning of this section. One easily sees that
> $r(k, l)$ can be thought of as the smallest integer $n$ such that every 2-edge
> colouring $(E_1, E_2)$ of $K_n$ contains either a complete subgraph on $k$
> vertices, all of whose edges are in colour 1, or a complete subgraph on $l$
> vertices, all of whose edges are in colour 2. Expressed in this form, the Ramsey
> numbers have a natural generalisation.

## In Lean notation

A total function `Sym2 (Fin n) → Fin m` — colouring every pair, including the
diagonal, which is harmless since `IsRamseyBoundMulti` only inspects `s(u,v)` for
`u ≠ v`.

⚠ **Not** Mathlib's `SimpleGraph.Coloring`, which colours *vertices*.  Also not
chapter 6's `G.edgeSet → Fin k`, which is partial (defined only on actual edges);
here the host graph is `Kₙ`, so every pair is an edge and a total function is
right.

"One easily sees" that the two formulations agree for `m = 2` — but this file
**does not state that equivalence**, so `ramseyNumber` and `ramseyNumberMulti` at
`m = 2` are formally unrelated.  Anything wanting to move between §7.2's two
halves needs that bridge.
-/
abbrev EdgeColouring (n m : ℕ) : Type := Sym2 (Fin n) → Fin m

/-- `IsRamseyBoundMulti n c`: every `m`-edge-colouring of `Kₙ` has, for some `i`, a set of `c i`
vertices whose internal edges are all colour `i`. (NEEDED-TO-STATE.)

## Book definition (§7.2, p. 116) — verbatim

> We define $r(k_1, k_2, \ldots, k_m)$ to be the smallest integer $n$ such that
> every $m$-edge colouring $(E_1, E_2, \ldots, E_m)$ of $K_n$ contains, for some
> $i$, a complete subgraph on $k_i$ vertices, all of whose edges are in colour
> $i$.

## In Lean notation

Colour every pair of `n` points with one of `m` colours; once `n` is large
enough, some colour `i` covers all edges within some `kᵢ` points.

The target sizes are a function `c : Fin m → ℕ` rather than a list, which makes
`Function.update c i (c i - 1)` the natural way to express "decrement the `i`-th
argument" in Theorem 7.7 below.
-/
def IsRamseyBoundMulti {m : ℕ} (n : ℕ) (c : Fin m → ℕ) : Prop :=
  ∀ χ : EdgeColouring n m, ∃ i : Fin m, ∃ s : Finset (Fin n),
    #s = c i ∧ ∀ u ∈ s, ∀ v ∈ s, u ≠ v → χ s(u, v) = i

/-- The multicolour Ramsey number `r(k₁,…,k_m)`. (NEEDED-TO-STATE.)

## Book definition (§7.2, p. 116)

The least `n` for which every `m`-edge colouring of `Kₙ` yields a monochromatic
complete subgraph on `kᵢ` vertices in some colour `i` — see the verbatim text on
`IsRamseyBoundMulti` above.

## In Lean notation

⚠ Same `sInf ∅ = 0` trap as `ramseyNumber`, and **worse**: there is no
`exists_isRamseyBoundMulti` anywhere in the file.  So every `ramseyNumberMulti`
is provably `0` as things stand, which makes `ramseyMulti_recursion`,
`ramseyTriangle_*` and Schur's theorem in §7.4 all vacuous.

With `m = 2` this should reduce to `ramseyNumber`, but that bridge is unstated
(see `EdgeColouring`).

## Where it leads

`k₁ = … = k_m = 3` gives the sequence `rₙ` of exercise 7.2.3, which is what
Schur's theorem consumes in §7.4.
-/
noncomputable def ramseyNumberMulti {m : ℕ} (c : Fin m → ℕ) : ℕ :=
  sInf {n | IsRamseyBoundMulti n c}

-- Thm 7.7 (multicolour Ramsey recursion).
/-- ## Book statement (§7.2, p. 116) — verbatim

> *Theorem 7.7* $r(k_1, k_2, \ldots, k_m) \leq r(k_1 - 1, k_2, \ldots, k_m) +$
> $$r(k_1, k_2 - 1, \ldots, k_m) + \ldots + r(k_1, k_2, \ldots, k_m - 1) - m + 2$$

⚠ The book gives **no proof**:

> The following theorem and corollary generalise (7.7) and theorem 7.5, and can be
> proved in a similar manner. They are left as an exercise (7.2.2).

## In Lean notation

Generalises Theorem 7.4's recursion.  Fix `v` in a large `Kₙ` and classify the
other vertices by the colour of their edge to `v`.  If every colour class were
smaller than `r(…, kᵢ-1, …)`, the classes could not cover all vertices — which is
exactly what the bound arranges.  Some class is then big enough for a
monochromatic complete subgraph, and `v` extends it in colour `i`.

Stated additively (`+ m` on the left, `+ 2` on the right) to avoid the ℕ
subtraction `- m + 2`.

⚠ `Function.update c i (c i - 1)` still has an inner ℕ subtraction; `hc : ∀ i, 2 ≤ c i`
keeps it from truncating.

## Proof plan

As Theorem 7.4, with an `m`-way pigeonhole in place of the two-way one:
1. Show the sum bounds `IsRamseyBoundMulti`.
2. Fix `χ` and `v`; partition `Fin n \ {v}` by `χ s(v, ·)`.
3. Pigeonhole: some class `i` has `≥ r(update c i (c i - 1))` elements.
4. Recurse into that class, then `insert v` — all its edges to the class are
   colour `i` by construction.

## Status

`sorry`, and vacuous until `ramseyNumberMulti` is given an existence lemma (see
there).
-/
theorem ramseyMulti_recursion {m : ℕ} (hm : 0 < m) (c : Fin m → ℕ) (hc : ∀ i, 2 ≤ c i) :
    ramseyNumberMulti c + m ≤
      (∑ i : Fin m, ramseyNumberMulti (Function.update c i (c i - 1))) + 2 := by
  sorry

-- Cor 7.7 (multinomial bound).
/-- **Corollary 7.7.**  *`r(k₁+1, …, k_m+1) ≤ (k₁ + k₂ + … + k_m)! / (k₁! k₂! ⋯
k_m!)`.*

## Book statement (§7.2, p. 116) — verbatim

> *Corollary 7.7* $r(k_1 + 1, k_2 + 1, \ldots, k_m + 1) \leq \dfrac{(k_1 + k_2 + \ldots + k_m)!}{k_1! \, k_2! \ldots k_m!}$

Left as exercise 7.2.2 alongside Theorem 7.7, so no book proof.

## In Lean notation

Iterating Theorem 7.7 gives exactly the multinomial recursion, as the two-colour
case gave binomials in Theorem 7.5.

With `m = 2` this is Theorem 7.5, since `(k₁+k₂)!/(k₁!k₂!) = C(k₁+k₂, k₁)`.

⚠ The division is exact but is ℕ division in Lean; as with `card_perfectMatching_completeGraph`
in chapter 5, the proof should establish the *multiplied* form
`r(…) * ∏ kᵢ! ≤ (∑ kᵢ)!` and divide only at the end.

## Proof plan

Induction on `∑ kᵢ`, using `ramseyMulti_recursion` and the multinomial analogue
of Pascal's rule (`Nat.multinomial` and its recurrence, if Mathlib provides one —
otherwise expand as iterated binomials).

## Status

`sorry`, and vacuous pending the multi-colour existence lemma.
-/
theorem ramseyMulti_le_multinomial {m : ℕ} (k : Fin m → ℕ) :
    ramseyNumberMulti (fun i => k i + 1) ≤ Nat.multinomial Finset.univ k := by
  sorry

-- Ex 7.2.1: r(k,l) = r(l,k).
/-- **Exercise 7.2.1.**  *For all `k` and `l`, `r(k, l) = r(l, k)`.*

## Book statement (§7.2, p. 116) — verbatim

> 7.2.1 Show that, for all $k$ and $l$, $r(k, l) = r(l, k)$.

An exercise, so the book gives no proof.  The underlying fact is stated in the
section opening (§7.2, p. 111):

> Clearly, $S$ is a clique of $G$ if and only if $S$ is an independent set of
> $G^c$, and so the two concepts are complementary.

## In Lean notation

Complementation swaps cliques and independent sets, so a graph with no `k`-clique
and no `l`-independent set becomes one with no `l`-clique and no `k`-independent
set.  The thresholds coincide.

Why the book's table is symmetric about its diagonal.

## Proof plan

1. `IsRamseyBound n k l ↔ IsRamseyBound n l k` via `G ↦ Gᶜ`, using
   `SimpleGraph.isNClique_compl_iff`-style transport between
   `IsNClique`/`IsNIndepSet` (Mathlib has `isIndepSet_compl_iff` or similar —
   check the exact name).
2. Equal sets ⇒ equal `sInf`.

✅ Needs **no** existence lemma: it is an equality of two `sInf`s over sets shown
equal, so it holds even in the degenerate `sInf ∅ = 0` case.  One of the few
§7.2 results that is not vacuous as things stand.

## Status

`sorry`.  ⭐ Genuinely reachable now — worth doing early.
-/
theorem ramseyNumber_comm (k l : ℕ) :
    SimpleGraph.ramseyNumber k l = SimpleGraph.ramseyNumber l k := by
  sorry

/-- `rₙ = r(3, …, 3)` with `n` colours.

## Book definition (exercise 7.2.3, p. 116) — verbatim

> **7.2.3** Let $r_n$ denote the Ramsey number $r(k_1, k_2, \ldots, k_n)$ with
> $k_i = 3$ for all $i$.

## In Lean notation

The least number of points such that any `n`-colouring of the pairs forces a
monochromatic *triangle*.  `r₂ = r(3,3) = 6`; Greenwood and Gleason showed
`r₃ = 17`.

Exactly what Schur's theorem (§7.4) consumes.

⚠ Inherits `ramseyNumberMulti`'s missing existence lemma, so `ramseyTriangle n`
is currently provably `0` for every `n`.
-/
noncomputable def ramseyTriangle (n : ℕ) : ℕ := ramseyNumberMulti (fun _ : Fin n => 3)

-- Ex 7.2.3(a): rₙ ≤ n(rₙ₋₁ − 1) + 2.
/-- ## Book statement (§7.2, p. 116) — verbatim

> &nbsp;($a$) Show that $r_n \leq n(r_{n-1} - 1) + 2$.

An exercise, so the book gives no proof.

## In Lean notation

Theorem 7.7 with all targets `3`.  Fix `v` in a `Kₙ` on `n(r_{n-1}-1) + 2`
vertices; its `n(r_{n-1}-1) + 1` neighbours split among `n` colours, so some
class has `≥ r_{n-1}` vertices.  Either two of them are joined in that same
colour — a monochromatic triangle with `v` — or the class avoids that colour and
its induced colouring uses only `n-1` colours, where `r_{n-1}` vertices force a
triangle.

Stated additively (`+ n` on the left) to avoid ℕ subtraction.

## Proof plan

The specialisation of `ramseyMulti_recursion` at `c ≡ 3`; the pigeonhole and
`insert v` steps are the same.  Worth proving directly rather than instantiating,
since the constant targets simplify `Function.update` away.

## Status

`sorry`, and vacuous pending the multi-colour existence lemma.
-/
theorem ramseyTriangle_recursion {n : ℕ} (hn : 1 ≤ n) :
    ramseyTriangle n + n ≤ n * ramseyTriangle (n - 1) + 2 := by
  sorry

-- Ex 7.2.3(b): rₙ ≤ [n! e] + 1.
/-- ## Book statement (§7.2, p. 116) — verbatim

> &nbsp;($b$) Noting that $r_2 = 6$, use ($a$) to show that
> $r_n \leq [n! \, e] + 1$.

An exercise, so the book gives no proof.  Here `[·]` is the **floor**.

## In Lean notation

Unwinding `rₙ ≤ n(r_{n-1} - 1) + 2` from `r₂ = 6` and dividing by `n!` gives a
telescoping sum of reciprocals `1/k!`, which converge to `e`.  Hence
`rₙ - 1 ≤ n! e`.

`e` appears precisely as `∑ 1/k!`.

## Proof plan

1. Set `aₙ = rₙ - 1`; part (a) becomes `aₙ ≤ n·a_{n-1} + 1`.
2. Divide by `n!`: `aₙ/n! ≤ a_{n-1}/(n-1)! + 1/n!`, a telescoping bound.
3. Sum from the base `a₂ = 5`, giving `aₙ/n! ≤ 5/2 + ∑_{k=3}^{n} 1/k! < e`.
4. `Nat.le_floor` to land the ℕ-valued conclusion.

⚠ Genuinely analytic — `Real.exp 1` and `⌊·⌋₊`, plus a bound on the tail of the
exponential series.  Mathlib has `Real.exp_eq_exp_ℝ`/`Real.add_one_le_exp` and
the series, but the specific comparison `5/2 + ∑_{k≥3} 1/k! < e` needs assembling.

## Status

`sorry`, and vacuous pending the multi-colour existence lemma.  The hardest
arithmetic in §7.2 after Theorem 7.6.
-/
theorem ramseyTriangle_le_factorial_exp {n : ℕ} (hn : 2 ≤ n) :
    ramseyTriangle n ≤ ⌊(Nat.factorial n : ℝ) * Real.exp 1⌋₊ + 1 := by
  sorry

-- Ex 7.2.3(c): r₃ ≤ 17.
/-- ## Book statement (§7.2, p. 116) — verbatim

> &nbsp;($c$) Deduce that $r_3 \leq 17$.
> (Greenwood and Gleason, 1955 have shown that $r_3 = 17$.)

An exercise, so the book gives no proof.

## In Lean notation

Part (a) at `n = 3` with `r₂ = 6`: `r₃ ≤ 3(6-1) + 2 = 17`.  (Part (b) also gives
`⌊6e⌋ + 1 = 16 + 1 = 17`.)

So among any seventeen points, any 3-colouring of the pairs forces a
monochromatic triangle.

## Proof plan

✅ **Use part (a), not part (b)** — `3·(6-1) + 2 = 17` is pure arithmetic, whereas
part (b) drags in `Real.exp`.

1. `ramseyTriangle_recursion` at `n = 3`.
2. `r₂ = 6` — ⚠ **not stated in this file.**  `six_le_ramseyNumber_three_three`
   gives only `6 ≤ r(3,3)`, is about `ramseyNumber` not `ramseyTriangle`, and is
   a lower bound where an upper one is needed.  So `r₂ = 6` must be added,
   including the `ramseyNumber ↔ ramseyNumberMulti` bridge at `m = 2`.
3. `omega`.

## Status

`sorry`.  Step 2 is a real gap, not a lookup — this is the input Schur's theorem
in §7.4 ultimately rests on.
-/
theorem ramseyTriangle_three_le : ramseyTriangle 3 ≤ 17 := by
  sorry

/-- The composition (lexicographic product) `G[H]`. (NEEDED-TO-STATE.)

## Book definition (exercise 7.2.4, p. 116) — verbatim

> 7.2.4 The *composition* of simple graphs $G$ and $H$ is the simple graph $G[H]$
> with vertex set $V(G) \times V(H)$, in which $(u, v)$ is adjacent to
> $(u', v')$ if and only if either $uu' \in E(G)$ or $u = u'$ and
> $vv' \in E(H)$.

## In Lean notation

Replace each vertex of `G` by a copy of `H`.  Vertices in *different* copies are
joined iff the corresponding `G`-vertices are adjacent; within one copy, iff
adjacent in `H`.  The `G`-structure dominates — hence the alternative name
*lexicographic product*.

✅ Fully defined, `symm` and `loopless` both discharged — no `sorry`.

⚠ Distinct from chapter 6's `boxProd` (`G □ H`), where within-copy and
across-copy edges are treated symmetrically.  Composition is not commutative.

## Where it is used

Parts (b) and (c) of the exercise, to multiply Ramsey lower bounds.
-/
def composition {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V × W) where
  Adj p q := G.Adj p.1 q.1 ∨ (p.1 = q.1 ∧ H.Adj p.2 q.2)
  symm := by
    rintro ⟨u, v⟩ ⟨u', v'⟩ (h | ⟨h1, h2⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨h1.symm, h2.symm⟩
  loopless := by
    rintro ⟨u, v⟩ (h | ⟨-, h⟩)
    · exact G.loopless u h
    · exact H.loopless v h

-- Ex 7.2.4(a): α(G[H]) ≤ α(G)·α(H).
/-- **Exercise 7.2.4(a).**  *`α(G[H]) ≤ α(G)α(H)`.*

## Book statement (§7.2, p. 116) — verbatim

> &nbsp;($a$) Show that $\alpha(G[H]) \leq \alpha(G)\alpha(H)$.

An exercise, so the book gives no proof.

## In Lean notation

Let `S` be independent in `G[H]`.  Its first-coordinate projection is independent
in `G` (two `S`-vertices in different copies force those `G`-vertices
non-adjacent), so at most `α(G)` copies are touched; within each, at most `α(H)`
vertices.  Multiply.

## Proof plan

1. Take `S` attaining `α(G[H])`.
2. `S.image Prod.fst` is independent in `G` — from the `Adj` definition's first
   disjunct.
3. For each `u` in that image, the fibre `{v | (u,v) ∈ S}` is independent in `H` —
   from the second disjunct.
4. `S.card ≤ (image).card * max fibre ≤ α(G) * α(H)` via
   `Finset.card_le_card_of_...`/`Finset.card_biUnion_le`.

⚠ Step 4 needs `S` decomposed as a `biUnion` over its projection, and each fibre
bounded uniformly — `Finset.card_eq_sum_card_fiberwise` is the usual tool.

## Status

`sorry`.  ✅ Self-contained — no Ramsey existence needed, since it is purely
about `indepNum`.
-/
theorem indepNum_composition_le {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (G.composition H).indepNum ≤ G.indepNum * H.indepNum := by
  sorry

-- Ex 7.2.4(b): Ramsey product lower bound.
/-- **Exercise 7.2.4(b).**  *`r(kl+1, kl+1) - 1 ≥ (r(k+1, k+1) - 1)(r(l+1, l+1) -
1)`.*

## Book statement (§7.2, p. 116) — verbatim

> &nbsp;($b$) Using ($a$), show that
> $$r(kl + 1, kl + 1) - 1 \geq (r(k + 1, k + 1) - 1) \times (r(l + 1, l + 1) - 1)$$

An exercise, so the book gives no proof.

## In Lean notation

Take `(k+1,k+1)`- and `(l+1,l+1)`-Ramsey graphs `G`, `H` — so `ω, α ≤ k` and
`≤ l` respectively — and form `G[H]`, which has the product vertex count.  Part
(a) gives `α(G[H]) ≤ kl`; complementing gives `ω(G[H]) ≤ kl`.  So `G[H]` avoids
both a `(kl+1)`-clique and a `(kl+1)`-independent set.

Stated additively (`… + 1 ≤ r(…)`) to avoid ℕ subtraction on the outside — though
the two inner `- 1`s remain.

⚠ The complement step needs `(G[H])ᶜ ≅ Gᶜ[Hᶜ]`, which is **true but not
obvious** and is not stated in this file.  Without it, part (a) bounds only `α`
and the clique side has to be argued separately.

## Proof plan

1. Extract Ramsey graphs at `k+1` and `l+1` from the definition of
   `ramseyNumber` — i.e. `¬ IsRamseyBound (r - 1) …`, which needs
   `Nat.not_mem_of_lt_sInf`.
2. Form the composition; count vertices.
3. `α ≤ kl` by part (a); `ω ≤ kl` via the complement identity above.
4. Conclude `¬ IsRamseyBound (product) (kl+1) (kl+1)`, hence the bound.

## Status

`sorry`, and vacuous pending `exists_isRamseyBound` — step 1 extracts nothing if
every `ramseyNumber` is `0`.
-/
theorem ramsey_product_lower {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) :
    (SimpleGraph.ramseyNumber (k + 1) (k + 1) - 1) * (SimpleGraph.ramseyNumber (l + 1) (l + 1) - 1)
      + 1 ≤ SimpleGraph.ramseyNumber (k * l + 1) (k * l + 1) := by
  sorry

-- Ex 7.2.4(c) (Abbott): 5^n + 1 ≤ r(2^n+1, 2^n+1).
/-- **Exercise 7.2.4(c)** (Abbott).  *`r(2ⁿ+1, 2ⁿ+1) ≥ 5ⁿ + 1` for all `n ≥ 0`.*

## Book statement (§7.2, p. 116) — verbatim

> &nbsp;($c$) Deduce that $r(2^n + 1, 2^n + 1) \geq 5^n + 1$ for all $n \geq 0$.
> (H. L. Abbott)

An exercise, so the book gives no proof.

## In Lean notation

Iterate part (b) from `r(3,3) = 6`, so `r(3,3) - 1 = 5`.  Taking `k = l = 2^{n-1}`
each step multiplies by `5`.  The witness is the `n`-fold composition of `C₅`
with itself.

## Proof plan

Induction on `n`: base `n = 0` is `2 ≤ r(2,2)`; step applies
`ramsey_product_lower` at `k = l = 2^{n-1}` together with `r(3,3) = 6`.

⚠ Needs `r(3,3) = 6` — only `6 ≤ r(3,3)` is available here (see
`six_le_ramseyNumber_three_three`), and the *upper* bound is what the induction
consumes.

## Significance (§7.2, p. 116)

The best **constructive** bound, versus Corollary 7.6's probabilistic one.  With
`k = 2ⁿ`, `5ⁿ = k^{log₂5} ≈ k^{2.32}` is merely polynomial in `k`, while `2^{k/2}`
is exponential — the gap the book remarks on.

## Status

`sorry`, blocked on part (b) and on `r(3,3) = 6`.
-/
theorem abbott_lower_bound (n : ℕ) :
    5 ^ n + 1 ≤ SimpleGraph.ramseyNumber (2 ^ n + 1) (2 ^ n + 1) := by
  sorry

/-- `C₃ ∨ C₅` on the carrier `Fin 3 ⊕ Fin 5`.

## Book context (exercise 7.2.5, p. 117) — verbatim

> **7.2.5** Show that the join of a 3-cycle and a 5-cycle contains no $K_6$, but
> that every 2-edge colouring yields a monochromatic triangle.
> (R. L. Graham)

## In Lean notation

`C₃ ∨ C₅` on `Fin 3 ⊕ Fin 5`: two disjoint cycles with every vertex of one joined
to every vertex of the other, on `8` vertices.

A *small* graph with no `K₆` in which every 2-edge colouring still forces a
monochromatic triangle — so "contains `K₆`" is not necessary for the Ramsey
property.

✅ An `abbrev` built from `join` and `cycleGraph`, fully defined.
-/
abbrev grahamGraph : SimpleGraph (Fin 3 ⊕ Fin 5) :=
  (SimpleGraph.cycleGraph 3).join (SimpleGraph.cycleGraph 5)

/-- The generalised Ramsey number `r(G₁,…,G_m)` over Mathlib's containment `⊑`. (NEEDED-TO-STATE.)

## Book definition (exercise 7.2.6, p. 117) — verbatim

> **7.2.6** Let $G_1, G_2, \ldots, G_m$ be simple graphs. The *generalised Ramsey
> number* $r(G_1, G_2, \ldots, G_m)$ is the smallest integer $n$ such that every
> $m$-edge colouring $(E_1, E_2, \ldots, E_m)$ of $K_n$ contains, for some $i$, a
> subgraph isomorphic to $G_i$ in colour $i$.

## In Lean notation

Instead of a monochromatic *complete* subgraph, a monochromatic copy of a
prescribed graph.  All `Gᵢ` complete recovers `ramseyNumberMulti`.

"Subgraph isomorphic to `Gᵢ`" is Mathlib's containment `⊑`, and the colour-`i`
graph is `fromEdgeSet {e | χ e = i ∧ ¬ e.IsDiag}` — the `¬ IsDiag` guard being
what stops the diagonal from creating spurious loops.

⚠ Same `sInf ∅ = 0` trap again, with **no** existence lemma for this notion
either.  So all four generalised-Ramsey results below are vacuous as stated.

⚠ The graphs are indexed by `W : Fin m → Type*`, so each `Gᵢ` may live on a
different carrier — flexible, but it means `![pathGraph 4, pathGraph 4]` below
must elaborate its motive carefully.
-/
noncomputable def generalisedRamseyNumber {m : ℕ} {W : Fin m → Type*}
    (F : ∀ i, SimpleGraph (W i)) : ℕ :=
  sInf {n | ∀ χ : Sym2 (Fin n) → Fin m,
    ∃ i, F i ⊑ SimpleGraph.fromEdgeSet {e | χ e = i ∧ ¬ e.IsDiag}}

-- Ex 7.2.6(b)* sub-lemma (ABSENT from Mathlib): δ ≥ m−1 ⇒ every m-vertex tree embeds.
/-- **Sub-lemma for exercise 7.2.6(b)*** (absent from Mathlib).  *If `δ(G) ≥ m - 1`
then every tree `T` on `m` vertices embeds in `G`.*

## Book context

Not stated in the book — extracted because parts (b) and (c) of exercise 7.2.6
both need it, and **Mathlib does not have it**.

## In Lean notation

Build the embedding greedily.  A tree on `m` vertices can be listed so each new
vertex attaches to exactly one already-placed vertex (peel leaves).  Placing the
`j`-th, its unique placed neighbour has `≥ m - 1` neighbours in `G`, of which at
most `j - 1 ≤ m - 2` are used — a fresh image always exists.

The standard "minimum degree forces every small tree" lemma; it is what makes
tree-target Ramsey numbers exactly computable.

⚠ `m` is a free variable in the signature, tied to `W` only through
`hm : Fintype.card W = m` — so `m` is determined but Lean will not infer it;
callers must supply it.

## Proof plan

1. Order `W` as `w₀, …, w_{m-1}` so each `wⱼ` (`j ≥ 1`) has exactly one
   `T`-neighbour among its predecessors.  ⚠ This ordering lemma for trees is
   itself not in Mathlib and is the real prerequisite — it is essentially "every
   finite tree has a leaf" iterated (`Trees.lean`'s `tree_two_leaves`).
2. Greedy induction on `j`, maintaining an injective partial map.
3. Assemble into `T ⊑ G`.

## Status

`sorry`.  Step 1 is a reusable piece of tree infrastructure worth stating
separately.
-/
theorem tree_isContained_of_minDegree_le
    {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} [DecidableRel G.Adj]
    {T : SimpleGraph W} (hT : T.IsTree) (hm : Fintype.card W = m)
    (hδ : m - 1 ≤ G.minDegree) :
    T ⊑ G := by
  sorry

-- Ex 7.2.6(b)*: r(T, K_{1,n}) = m + n − 1.
-- NOTE: `![T, K_{1,n}]` cannot elaborate across heterogeneous carriers (`vecCons` is homogeneous);
-- the argument is spelled as a dependent 2-vector `Fin.cons T (Fin.cons _ finZeroElim)` with an
-- explicit type family `W := ![W, Fin 1 ⊕ Fin n]`.  (`W : Type` rather than `Type*` for the family.)
/-- **Exercise 7.2.6(b)***.  *If `T` is any tree on `m` vertices and `m - 1`
divides `n - 1`, then `r(T, K_{1,n}) = m + n - 1.*

## Book statement (§7.2, p. 117) — verbatim

> $(b)^*$ if $T$ is any tree on $m$ vertices and if $m - 1$ divides $n - 1$, then
> $r(T, K_{1,n}) = m + n - 1$;
> (V. Chvátal)

A starred exercise, so the book gives no proof.

## In Lean notation

`K_{1,n}` is the **star** with `n` leaves, so a blue copy is a vertex with `n`
blue edges.  On `m + n - 1` points, if no vertex has `n` blue edges then every
vertex has `≥ (m+n-2) - (n-1) = m - 1` red edges, and
`tree_isContained_of_minDegree_le` embeds `T` in red.

Lower bound: a colouring of `K_{m+n-2}` with no red `T` and no blue star.  The
divisibility `(m-1) ∣ (n-1)` is exactly what lets the red graph be
`(m-2)`-regular — too sparse for `T`, while leaving every vertex under `n` blue
edges.

⚠ The two targets live on **different carriers** (`W` and `Fin 1 ⊕ Fin n`), so
`![T, K_{1,n}]` cannot elaborate — `Matrix.vecCons` is homogeneous.  Hence the
dependent spelling `Fin.cons T (Fin.cons _ finZeroElim)` with an explicit type
family `W := ![W, Fin 1 ⊕ Fin n]`, and `W : Type` rather than `Type*`.

## Proof plan

Upper bound as above via the sub-lemma; lower bound by the explicit regular
colouring.

## Status

`sorry`, depends on `tree_isContained_of_minDegree_le`, and vacuous pending
existence.
-/
theorem generalisedRamsey_tree_star
    {W : Type} [Fintype W] {T : SimpleGraph W} (hT : T.IsTree)
    {m n : ℕ} (hm : Fintype.card W = m) (hdvd : (m - 1) ∣ (n - 1)) :
    generalisedRamseyNumber (W := ![W, Fin 1 ⊕ Fin n])
        (Fin.cons T (Fin.cons (completeBipartiteGraph (Fin 1) (Fin n)) finZeroElim))
      = m + n - 1 := by
  sorry

-- Ex 7.2.6(c)* (Chvátal): r(T, Kₙ) = (m−1)(n−1) + 1.  (Same heterogeneous-vector NOTE as above.)
/-- **Exercise 7.2.6(c)*** (Chvátal).  *If `T` is any tree on `m` vertices, then
`r(T, Kₙ) = (m-1)(n-1) + 1`.*

## Book statement (§7.2, p. 117) — verbatim

> $(c)^*$ if $T$ is any tree on $m$ vertices, then
> $r(T, K_n) = (m - 1)(n - 1) + 1$.
> (V. Chvátal)

A starred exercise, so the book gives no proof.

## In Lean notation

One of the cleanest results in generalised Ramsey theory: the answer depends on
the tree only through its **number of vertices**, not its shape.

*Lower bound.*  Partition `(m-1)(n-1)` points into `n-1` groups of `m-1`; red
inside groups, blue between.  Red is a disjoint union of `K_{m-1}`s, too small
for a tree on `m` vertices; blue is complete `(n-1)`-partite, so its largest
clique has `n-1` vertices — no `Kₙ`.

*Upper bound.*  On `(m-1)(n-1) + 1` points, if blue has no `Kₙ` then Turán-type
reasoning gives red minimum degree `≥ m-1` somewhere, and the sub-lemma embeds
`T`.

⚠ Same heterogeneous-carrier spelling as part (b).

⚠ The upper bound's "Turán-type reasoning" is genuinely §7.3's Theorem 7.9 —
so this exercise depends on the *next* section, not just on §7.2.

## Proof plan

Lower bound by the explicit partition colouring; upper bound via Theorem 7.9 plus
`tree_isContained_of_minDegree_le`.

## Status

`sorry`, depends on the sub-lemma and on Turán, and vacuous pending existence.
-/
theorem chvatal_tree_complete
    {W : Type} [Fintype W] {T : SimpleGraph W} (hT : T.IsTree)
    {m n : ℕ} (hm : Fintype.card W = m) (hn : 1 ≤ n) :
    generalisedRamseyNumber (W := ![W, Fin n])
        (Fin.cons T (Fin.cons (⊤ : SimpleGraph (Fin n)) finZeroElim))
      = (m - 1) * (n - 1) + 1 := by
  sorry

/-! # §7.3 — Turán's Theorem -/

-- Thm 7.8 (Erdős degree-majorisation): a K_{m+1}-free graph is degree-majorised by a complete
-- multipartite graph, with equality of degree sequences forcing isomorphism.
/-- **Theorem 7.8** (Erdős, 1970).  *If a simple graph `G` contains no `K_{m+1}`,
then `G` is degree-majorised by some complete `m`-partite graph `H`.  Moreover, if
`G` has the same degree sequence as `H`, then `G ≅ H`.*

## Book statement (§7.3, p. 117) — verbatim

> **Theorem 7.8** If a simple graph $G$ contains no $K_{m+1}$, then $G$ is
> degree-majorised by some complete $m$-partite graph $H$. Moreover, if $G$ has
> the same degree sequence as $H$, then $G \cong H$.

## Book proof (§7.3, pp. 117–118) — verbatim

> By induction on $m$. The theorem is trivial for $m = 1$. Assume that it holds
> for all $m < n$, and let $G$ be a simple graph which contains no $K_{n+1}$.
> Choose a vertex $u$ of degree $\Delta$ in $G$, and set $G_1 = G[N(u)]$. Since
> $G$ contains no $K_{n+1}$, $G_1$ contains no $K_n$ and therefore, by the
> induction hypothesis, is degree-majorised by some complete $(n-1)$-partite graph
> $H_1$.
>
> Next, set $V_1 = N(u)$ and $V_2 = V \backslash V_1$, and denote by $G_2$ the
> graph whose vertex set is $V_2$ and whose edge set is empty. Consider the join
> $G_1 \vee G_2$ of $G_1$ and $G_2$. Since
> $$N_G(v) \subseteq N_{G_1 \vee G_2}(v) \quad \text{for} \quad v \in V_1 \tag{7.15}$$
> and since each vertex of $V_2$ has degree $\Delta$ in $G_1 \vee G_2$, $G$ is
> degree-majorised by $G_1 \vee G_2$. Therefore $G$ is also degree-majorised by the
> complete $n$-partite graph $H = H_1 \vee G_2$.
>
> Suppose, now, that $G$ has the same degree sequence as $H$. Then $G$ has the
> same degree sequence as $G_1 \vee G_2$ and hence equality must hold in (7.15).
> Thus, in $G$, every vertex of $V_1$ must be joined to every vertex of $V_2$. It
> follows that $G = G_1 \vee G_2$. Since $G = G_1 \vee G_2$ has the same degree
> sequence as $H = H_1 \vee G_2$, the graphs $G_1$ and $H_1$ must have the same
> degree sequence and therefore, by the induction hypothesis, be isomorphic. We
> conclude that $G \cong H$.

## In Lean notation

The book remarks (§7.3, p. 118) on the parallel with Theorem 4.6:

> It is interesting to note that the above theorem bears a striking similarity to
> theorem 4.6.

⚠ **Blocked on `degreeSequence` being unsorted** — see the warning there.  The
book's `DegreeMajorised` compares *nondecreasing* sequences; against this file's
unsorted list the predicate is not even isomorphism-invariant, so the equality
clause (`same degree sequence → G ≅ H`) cannot be right as stated.  Fix
`degreeSequence` first.

⚠ The carrier changes: `H` is existentially quantified over a fresh type `W`, so
`DegreeMajorised G H` compares across types via the `Fintype.card V = Fintype.card W`
conjunct.

## Proof plan

1. Induction on `m`.
2. `G₁ = G.induce (G.neighborSet u)` for `u` of maximum degree; `CliqueFree m`
   follows from `CliqueFree (m+1)` on `G`.
3. Build `H = H₁ ∨ G₂` using `join`; carrier `W₁ ⊕ V₂`.
4. Degree domination (7.15) then `degreeMajorised_of_forall_degree_le` — ⚠ but
   that sub-lemma is stated for `G H : SimpleGraph V` on the **same** carrier,
   whereas here the carriers differ.  It does not apply as stated.
5. Equality clause by a second induction.

## Status

`sorry`.  ⭐ The chapter's structural core, and currently blocked on two
infrastructure defects (unsorted `degreeSequence`, same-carrier sub-lemma) rather
than on mathematics.
-/
theorem degreeMajorised_of_cliqueFree
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ} (hm : 1 ≤ m)
    (h : G.CliqueFree (m + 1)) :
    ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      H.IsCompleteMultipartite ∧ DegreeMajorised G H ∧
      (G.degreeSequence = H.degreeSequence → Nonempty (G ≃g H)) := by
  sorry

-- Thm 7.8 sub-lemma (ABSENT): pointwise degree domination ⇒ degree-majorisation (the "and since").
/-- **Sub-lemma for theorem 7.8** (absent from Mathlib).  *If `d_G(v) ≤ d_H(v)` for
every vertex `v`, then `G` is degree-majorised by `H`.*

## Book context (§7.3, p. 117)

Not stated separately — this is the step Theorem 7.8's proof passes over, where
it concludes degree-majorisation from `N_G(v) ⊆ N_{G_1 \vee G_2}(v)`:

> and since each vertex of $V_2$ has degree $\Delta$ in $G_1 \vee G_2$, $G$ is
> degree-majorised by $G_1 \vee G_2$.

## In Lean notation

Degree-majorisation compares *sorted* sequences entrywise.  Pointwise domination
survives sorting: the `i`-th smallest degree of `G` cannot exceed the `i`-th
smallest of `H`.

⚠ **Two problems with this as stated.**

1. `degreeSequence` in this file is **unsorted**, so "sorting preserves
   domination" is not what the predicate says — the entrywise comparison is
   against `Finset.univ.toList`'s arbitrary order.  With both graphs on the same
   `V` that order is at least *the same* on both sides, so pointwise domination
   does happen to give the conclusion — but only by accident of the shared
   carrier, not because the lemma is right.
2. It is stated for `G H : SimpleGraph V` on the **same** carrier, whereas
   Theorem 7.8 needs it across different carriers (`G` on `V`, `H` on `W`).  So
   it does not actually discharge the step it was extracted for.

## Proof plan

As stated (same carrier, unsorted lists) it is nearly immediate:
`Fintype.card V = Fintype.card V` and `List.getD` of two `map`s over the same
`toList`, so `h` applies entrywise.

To be *useful*, restate over sorted sequences and across carriers.

## Status

`sorry`.  Fix `degreeSequence` and the carrier generality before proving —
otherwise this proves something true but useless.
-/
theorem degreeMajorised_of_forall_degree_le {V : Type*} [Fintype V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : ∀ v, G.degree v ≤ H.degree v) : DegreeMajorised G H := by
  sorry

-- Thm 7.9 (TURÁN), first half (WRAPPER over `CliqueFree.card_edgeFinset_le`).
/-- **Theorem 7.9** (Turán, 1941), first half.  *If `G` is simple and contains no
`K_{m+1}`, then `ε(G) ≤ ε(T_{m,ν})`*, where `T_{m,ν}` is the complete `m`-partite
graph on `ν` vertices with all parts as equal in size as possible.

## Book statement (§7.3, p. 118) — verbatim

> **Theorem 7.9** If $G$ is simple and contains no $K_{m+1}$, then
> $\varepsilon(G) \le \varepsilon(T_{m,\nu})$. Moreover,
> $\varepsilon(G) = \varepsilon(T_{m,\nu})$ only if $G \cong T_{m,\nu}$.

with (§7.3, p. 118):

> Let $T_{m,n}$ denote the complete $m$-partite graph on $n$ vertices in which all
> parts are as equal in size as possible.

## Book proof (§7.3, p. 119) — verbatim, first half

> Let $G$ be a simple graph that contains no $K_{m+1}$. By theorem 7.8, $G$ is
> degree-majorised by some complete $m$-partite graph $H$. It follows from theorem
> 1.1 that
> $$\varepsilon(G) \le \varepsilon(H) \tag{7.16}$$
> But (exercise 1.2.9)
> $$\varepsilon(H) \le \varepsilon(T_{m,\nu}) \tag{7.17}$$
> Therefore, from (7.16) and (7.17)
> $$\varepsilon(G) \le \varepsilon(T_{m,\nu}) \tag{7.18}$$
> proving the first assertion.

## Proof plan

✅ **Do not follow the book.**  Mathlib has Turán's theorem in full
(`Combinatorics/SimpleGraph/Extremal/Turan.lean`), including
`turanGraph n r` — the same graph, defined as `Adj v w := v % r ≠ w % r`.

The relevant result is

    theorem CliqueFree.card_edgeFinset_le (cf : G.CliqueFree (r + 1)) :
        #G.edgeFinset ≤ (n^2 - (n % r)^2) * (r - 1) / (2 * r) + (n % r).choose 2

⚠ That is a **closed-form arithmetic** bound, not the `≤ #(turanGraph …).edgeFinset`
stated here.  The bridge is `card_edgeFinset_turanGraph`, which computes
`#(turanGraph n r).edgeFinset` to exactly that expression.  So:

    h.card_edgeFinset_le  |>.trans_eq card_edgeFinset_turanGraph.symm

modulo the `let n := …` binder in Mathlib's statement.

This makes Theorem 7.9 reachable **without** Theorem 7.8 — which matters, since
7.8 is blocked on the unsorted-`degreeSequence` defect.

## Significance (§7.3, p. 117) — verbatim

> Turán's theorem has become the basis of a significant branch of graph theory
> known as *extremal graph theory*.

## Status

`sorry`, but ⭐ **among the most tractable results in the chapter** — the hard
mathematics is already in Mathlib and only the arithmetic bridge remains.
-/
theorem turan_edge_bound
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ}
    (h : G.CliqueFree (m + 1)) :
    #G.edgeFinset ≤ #(SimpleGraph.turanGraph (Fintype.card V) m).edgeFinset := by
  sorry

-- Thm 7.9 (TURÁN), second half (uniqueness); rides `isTuranMaximal_iff_nonempty_iso_turanGraph`.
/-- **Theorem 7.9** (Turán, 1941), second half.  *`ε(G) = ε(T_{m,ν})` only if
`G ≅ T_{m,ν}`.*

## Book proof (§7.3, p. 119) — verbatim, second half

> Suppose, now, that equality holds in (7.18). Then equality must hold in both
> (7.16) and (7.17). Since $\varepsilon(G) = \varepsilon(H)$ and $G$ is
> degree-majorised by $H$, $G$ must have the same degree sequence as $H$.
> Therefore, by theorem 7.8, $G \cong H$. Also, since
> $\varepsilon(H) = \varepsilon(T_{m,\nu})$, it follows (exercise 1.2.9) that
> $H \cong T_{m,\nu}$. We conclude that $G \cong T_{m,\nu}$.

## In Lean notation

The balanced complete multipartite graph is not merely *an* extremal example but
the **unique** one, up to isomorphism.

## Proof plan

✅ Again Mathlib, not the book.  `isTuranMaximal_iff_nonempty_iso_turanGraph`
(`hr : 0 < r`) states

    G.IsTuranMaximal r ↔ Nonempty (G ≃g turanGraph (Fintype.card V) r)

so the work is producing `IsTuranMaximal m` from this statement's hypotheses:
1. `IsTuranMaximal` is "`CliqueFree (m+1)` **and** maximal edge count among such
   graphs".  The first conjunct is `h`.
2. The second follows from `heq` plus `turan_edge_bound`: any competing
   `K_{m+1}`-free graph has `#edgeFinset ≤ #turanGraph.edgeFinset = #G.edgeFinset`.
3. Then `(isTuranMaximal_iff_nonempty_iso_turanGraph hm).mp`.

⚠ `hm : 0 < m` is exactly Mathlib's `hr` and is genuinely needed — at `m = 0`,
`CliqueFree 1` forces `V` empty and the iso statement degenerates.

## Status

`sorry`, depends on `turan_edge_bound`.  Like it, ⭐ tractable — the substance is
in Mathlib.
-/
theorem turan_iso_of_card_edgeFinset_eq
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ} (hm : 0 < m)
    (h : G.CliqueFree (m + 1))
    (heq : #G.edgeFinset = #(SimpleGraph.turanGraph (Fintype.card V) m).edgeFinset) :
    Nonempty (G ≃g SimpleGraph.turanGraph (Fintype.card V) m) := by
  sorry

-- Ex 7.3.3(a) (near-WRAPPER): ν² < 4ε ⇒ a triangle.
/-- **Exercise 7.3.3(a).**  *If `G` is simple and `ε > ν²/4`, then `G` contains a
triangle.*

## Book statement (§7.3, p. 119) — verbatim

> **7.3.3**  $(a)$  Show that if $G$ is simple and $\varepsilon > \nu^2/4$, then
> $G$ contains a triangle.

An exercise, so the book gives no proof.

## In Lean notation

Turán at `m = 2` — Mantel's 1907 case, half a century before the
generalisation.  Extremal example: balanced `K_{⌊ν/2⌋,⌈ν/2⌉}` with `⌊ν²/4⌋`
edges.

Cleared to `ν² < 4ε` to avoid division.

## Proof plan

`by_contra` on `CliqueFree 3`, then `turan_edge_bound` at `m = 2`, then evaluate
`#(turanGraph ν 2).edgeFinset = ⌊ν²/4⌋` via `card_edgeFinset_turanGraph` and
`omega`.

⚠ The `ν²/4` versus `⌊ν/2⌋·⌈ν/2⌉` reconciliation is ℕ-division arithmetic and is
the only fiddly part.

## Status

`sorry`, depends on `turan_edge_bound` — so ⭐ tractable via Mathlib.
-/
theorem triangle_of_card_edgeFinset_gt
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : (Fintype.card V) ^ 2 < 4 * #G.edgeFinset) :
    ¬ G.CliqueFree 3 := by
  sorry

-- Ex 7.3.3(c)*: a non-bipartite graph with (ν−1)²+4 < 4ε has a triangle.
/-- **Exercise 7.3.3(c)***.  *If `G` is simple and not bipartite with
`ε > (ν-1)²/4 + 1`, then `G` contains a triangle.*

## Book statement (§7.3, p. 119) — verbatim

> $(c)^*$  Show that if $G$ is simple and not bipartite with
> $\varepsilon > ((\nu-1)^2/4)+1$, then $G$ contains a triangle.
> (P. Erdös)

A starred exercise, so the book gives no proof.

## In Lean notation

Forbidding bipartiteness on top of triangle-freeness drops the cap from `ν²/4` to
`(ν-1)²/4 + 1`.  A triangle-free non-bipartite graph contains an odd cycle of
length `≥ 5`, which is an inefficient use of vertices; the densest such graph is
essentially `C₅` blown up.

The **stability** phenomenon of extremal graph theory: near-extremal graphs all
resemble the extremal one, so departing from it costs edges.

Cleared to `(ν-1)² + 4 < 4ε`.

## Proof plan

⚠ **Not a corollary of Turán** — Turán bounds triangle-free graphs at `ν²/4` and
says nothing about the non-bipartite ones.  This needs its own argument:
1. `by_contra`: `G` triangle-free and non-bipartite.
2. Non-bipartite + triangle-free ⇒ an induced `C₅` (shortest odd cycle has
   length ≥ 5, and a shortest one is induced).
3. Count edges by splitting on the `C₅` and the rest, bounding cross-edges by
   triangle-freeness.

Substantially harder than parts (a)–(b), which is why the book stars it.

## Status

`sorry`.
-/
theorem triangle_of_not_bipartite_of_card_edgeFinset_gt
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hnb : ¬ G.IsBipartite)
    (h : (Fintype.card V - 1) ^ 2 + 4 < 4 * #G.edgeFinset) :
    ¬ G.CliqueFree 3 := by
  sorry

-- Ex 7.3.3(d): PLACEHOLDER — B&M gives no construction, so the def would be `sorry` (FORBIDDEN).
-- Commented out until a real witness graph is supplied (the exercise IS to find it).
/-
def erdosNonBipartiteExtremal (n : ℕ) : SimpleGraph (Fin n) := sorry -- ⚠ PLACEHOLDER, NOT A DEF

theorem erdosNonBipartiteExtremal_spec (n : ℕ) (hn : 5 ≤ n) :
    ¬ (erdosNonBipartiteExtremal n).IsBipartite ∧
    (erdosNonBipartiteExtremal n).CliqueFree 3 ∧
    #(erdosNonBipartiteExtremal n).edgeFinset = (n - 1) ^ 2 / 4 + 1 := by
  sorry
-/

/-! ### Book statement of the commented-out item

*Exercise 7.3.3(d)* (Erdős).  *Find a simple non-bipartite graph `G` with
`ε = ⌊(ν-1)²/4⌋ + 1` that contains no triangle.*

The witness is built from a 5-cycle by "blowing up" its vertices into
independent sets of nearly equal size, joining two blown-up sets exactly when the
corresponding vertices of `C₅` were adjacent.  The result is triangle-free
(inherited from the girth of `C₅`) and non-bipartite (the 5-cycle survives), and
a count shows it attains `⌊(ν-1)²/4⌋ + 1` edges — so the bound of part (c) is
sharp.

As the comment above records, the exercise *is* to find this graph, so writing it
as a `def … := sorry` would be a placeholder rather than a definition. -/

-- Ex 7.3.4(a)*: a degree double-count forces K_{2,m}.
/-- **Exercise 7.3.4(a)***.  *If `G` is simple and
`∑_{v ∈ V} C(d(v), 2) > (m-1)C(ν, 2)`, then `G` contains `K_{2,m}` (`m ≥ 2`).*

## Book statement (§7.3, p. 119) — verbatim

> **7.3.4**  $(a)^*$  Show that if $G$ is simple and
> $\displaystyle\sum_{v \in V} \binom{d(v)}{2} > (m-1)\binom{\nu}{2}$, then $G$
> contains $K_{2,m}(m \ge 2)$.

A starred exercise, so the book gives no proof.

## In Lean notation

Double-count **cherries** (paths of length two).  Each `v` centres `C(d(v),2)` of
them, so the total is `∑_v C(d(v),2)`; each is determined by its two *endpoints*,
an unordered pair from `C(ν,2)`.  If no pair had `m` common neighbours, each pair
would host `≤ m-1` cherries, capping the total at `(m-1)C(ν,2)`.

The prototype for Kővári–Sós–Turán (exercise 7.3.5).

## Proof plan

1. Define the cherry count as `∑ over pairs, (common neighbours).card`.
2. Show it equals `∑_v C(d(v),2)` — the double count, via
   `Finset.sum_comm` over (centre, endpoint-pair).
3. `by_contra`: every pair has `≤ m-1` common neighbours ⇒ total `≤ (m-1)C(ν,2)`,
   contradicting `h`.
4. So some pair has `≥ m` common neighbours — that pair plus those neighbours is
   a `K_{2,m}`; assemble the containment `⊑`.

⚠ Step 4's assembly needs the two endpoints to be *distinct from* the `m` common
neighbours, which holds since a vertex is not its own neighbour — but must be
said.

## Status

`sorry`.  The double count at step 2 is the substance.
-/
theorem isContained_completeBipartite_two_of_sum_choose_gt
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {m : ℕ} (hm : 2 ≤ m)
    (h : (m - 1) * (Fintype.card V).choose 2 < ∑ v : V, (G.degree v).choose 2) :
    completeBipartiteGraph (Fin 2) (Fin m) ⊑ G := by
  sorry

-- Ex 7.3.4(b): edge bound forcing K_{2,m} (real `rpow`).
/-- **Exercise 7.3.4(b).**  *Deduce that if `G` is simple and
`ε > ((m-1)^{1/2} ν^{3/2})/2 + ν/4`, then `G` contains `K_{2,m}` (`m ≥ 2`).*

## Book statement (§7.3, p. 119) — verbatim

> $(b)$  Deduce that if $G$ is simple and
> $\varepsilon > \dfrac{(m-1)^{\frac{1}{2}}\nu^{\frac{3}{2}}}{2} + \dfrac{\nu}{4}$,
> then $G$ contains $K_{2,m}(m \ge 2)$.

An exercise, so the book gives no proof.

## In Lean notation

Convert part (a)'s degree condition into an edge count.  By convexity,
`∑_v C(d(v),2)` is minimised at fixed `ε` when all degrees equal `2ε/ν`, so
`∑_v C(d(v),2) ≥ ν · C(2ε/ν, 2)`; demanding this exceed `(m-1)C(ν,2)` and solving
for `ε` gives the threshold.

A genuinely **sub-quadratic** threshold (`ν^{3/2}`), unlike Turán's for cliques.

⚠ Real-valued with `rpow` exponents, so the proof leaves ℕ early.  Mathlib's
`inner_mul_le_norm_mul_norm` or `Finset.inner_mul_le_norm_mul_norm` /
`sq_sum_le_card_mul_sum_sq` supply the convexity step; `Finset.inner_card_le_...`
is the usual shape for "sum of `C(dᵥ,2)` versus the average".

## Proof plan

1. Convexity: `∑ C(d(v),2) ≥ ν · C(2ε/ν, 2)` — Jensen, or Cauchy–Schwarz on
   `∑ d(v)² ≥ (∑ d(v))²/ν`.
2. Combine with `h` to contradict part (a)'s hypothesis being unmet.
3. Apply part (a).

## Status

`sorry`, depends on part (a) and on the convexity estimate.
-/
theorem isContained_completeBipartite_two_of_card_edgeFinset_gt
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {m : ℕ} (hm : 2 ≤ m)
    (h : ((m - 1 : ℝ)) ^ ((1 : ℝ) / 2) * (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) / 2
           + (Fintype.card V : ℝ) / 4 < (#G.edgeFinset : ℝ)) :
    completeBipartiteGraph (Fin 2) (Fin m) ⊑ G := by
  sorry

/-- The unit-distance graph on a finite point set in the plane. (NEEDED-TO-STATE; static.)

## Book context (exercise 7.3.4(c), p. 120) — verbatim

> $(c)$ Show that, given a set of $n$ points in the plane, the number of pairs of
> points at distance exactly 1 is at most $n^{\frac{3}{2}}/\sqrt{2}+n/4$.

The graph itself is the formaliser's construction; the book works directly with
the point set.

## In Lean notation

Join `i, j` when `dist (x i) (x j) = 1`.  Carrier `EuclideanSpace ℝ (Fin 2)`.

The geometry enters as a forbidden subgraph: two points have at most **two**
common unit-distance neighbours (two unit circles meet in ≤ 2 points), so the
graph has no `K_{2,3}`, and 7.3.4(b) bounds `ε`.

✅ Fully defined, `symm` and `loopless` both discharged — no `sorry`.

⚠ The `i ≠ j` conjunct in `Adj` is doing real work: without it, `dist (x i) (x i)
= 0 ≠ 1` would still exclude loops, but only if the `x i` are *distinct points*.
Since `x` is not assumed injective, two indices may carry the same point, and
`i ≠ j` is what keeps the graph simple in that case.
-/
def unitDistanceGraph {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 2)) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ Dist.dist (x i) (x j) = 1
  symm := by rintro i j ⟨h1, h2⟩; exact ⟨h1.symm, by rwa [_root_.dist_comm]⟩
  loopless := by rintro i ⟨h, -⟩; exact h rfl

-- Ex 7.3.4(c): unit-distance pairs in the plane are at most n^{3/2}/√2 + n/4.
/-- **Exercise 7.3.4(c).**  *Given a set of `n` points in the plane, the number of
pairs of points at distance exactly 1 is at most `n^{3/2}/√2 + n/4`.*

## Book statement (§7.3, p. 120) — verbatim

> $(c)$ Show that, given a set of $n$ points in the plane, the number of pairs of
> points at distance exactly 1 is at most $n^{\frac{3}{2}}/\sqrt{2}+n/4$.

An exercise, so the book gives no proof.

## In Lean notation

Two distinct points have `≤ 2` common unit-distance neighbours (two unit circles
meet in `≤ 2` points), so the graph is `K_{2,3}`-free; 7.3.4(b) at `m = 3` gives
`ε ≤ (√2 · n^{3/2})/2 + n/4 = n^{3/2}/√2 + n/4`.

A purely combinatorial bound on a geometric quantity, obtained by turning a fact
about circles into a forbidden subgraph.  The true order of growth of the
unit-distance problem is still open (Erdős).

## Proof plan

1. **The geometric input**: two distinct points of `ℝ²` have at most two points
   at distance `1` from both.  ⚠ This is the only genuinely geometric step and is
   **not in Mathlib** in this form — it is the statement that two distinct
   circles of equal radius meet in ≤ 2 points, which needs `EuclideanSpace`
   sphere-intersection reasoning.
2. Hence no `K_{2,3}` ⊑ the graph.
3. Contrapose 7.3.4(b) at `m = 3`.

## Status

`sorry`.  Step 1 is the obstacle — everything else is 7.3.4(b).
-/
theorem card_unit_distance_pairs_le
    {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 2))
    [DecidableRel (unitDistanceGraph x).Adj] :
    (#(unitDistanceGraph x).edgeFinset : ℝ)
      ≤ (n : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt 2 + (n : ℝ) / 4 := by
  sorry

-- Ex 7.3.5 (Kővári–Sós–Turán): edge bound forcing K_{m,m} (variable `rpow` exponent).
/-- **Exercise 7.3.5** (the Kővári–Sós–Turán theorem).  *If `G` is simple and
`ε > ((m-1)^{1/m} ν^{2-1/m})/2 + ((m-1)ν)/2`, then `G` contains `K_{m,m}`.*

## Book statement (§7.3, p. 120) — verbatim

> 7.3.5 Show that if $G$ is simple and
> $\varepsilon > \dfrac{(m-1)^{1/m}\nu^{2-1/m}}{2}+\dfrac{(m-1)\nu}{2}$ then $G$
> contains $K_{m,m}$.

An exercise, so the book gives no proof.  This is the **Kővári–Sós–Turán
theorem**.

## In Lean notation

Generalises 7.3.4 from `K_{2,m}` to `K_{m,m}`.  Count *stars* — a vertex with `m`
of its neighbours — two ways: each `v` contributes `C(d(v), m)`, and each
`m`-set can be the leaf-set of `≤ m-1` stars unless a `K_{m,m}` appears.
Convexity converts the degree sum into an edge count.

The exponent `2 - 1/m` is the point: forbidding a complete *bipartite* subgraph
caps `ε` at strictly sub-quadratic order, unlike Turán's constant fraction of
`ν²`.  Whether the exponent is tight for every `m` is the **Zarankiewicz
problem**, still open.

⚠ The `rpow` exponent varies with `m`, so this is irreducibly real-valued; and
`(m - 1 : ℝ)` with `hm : 1 ≤ m` means the base can be `0` at `m = 1`, where
`0 ^ (1/1) = 0` — check that boundary case does not make the hypothesis vacuous.

## Proof plan

The same double count as 7.3.4(a), with `m` in place of `2`, then the convexity
step of 7.3.4(b) generalised from `C(·,2)` to `C(·,m)`.

## Status

`sorry`.  The hardest analytic estimate in §7.3.
-/
theorem isContained_completeBipartite_of_card_edgeFinset_gt
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {m : ℕ} (hm : 1 ≤ m)
    (h : ((m - 1 : ℝ)) ^ ((1 : ℝ) / m) * (Fintype.card V : ℝ) ^ (2 - (1 : ℝ) / m) / 2
           + ((m : ℝ) - 1) * (Fintype.card V : ℝ) / 2 < (#G.edgeFinset : ℝ)) :
    completeBipartiteGraph (Fin m) (Fin m) ⊑ G := by
  sorry

/-! # §7.4 — Schur's Theorem -/

-- Thm 7.10 (Schur): any partition of {1,…,rₙ} into n parts has a part with x + y = z.
/-- **Theorem 7.10** (Schur, 1916).  *Let `(S₁, …, S_n)` be any partition of
`{1, 2, …, rₙ}`.  Then, for some `i`, `Sᵢ` contains three integers `x`, `y`, `z`
satisfying `x + y = z`.*

## Book statement (§7.4, p. 120) — verbatim

> **Theorem 7.10** Let $(S_1,S_2,\ldots,S_n)$ be any partition of the set of
> integers $\{1,2,\ldots,r_n\}$. Then, for some $i$, $S_i$ contains three integers
> $x$, $y$ and $z$ satisfying the equation $x+y=z$.

## Book proof (§7.4, p. 120) — verbatim

> Consider the complete graph whose vertex set is $\{1,2,\ldots,r_n\}$. Colour the
> edges of this graph in colours $1,2,\ldots,n$ by the rule that the edge $uv$ is
> assigned colour $j$ if and only if $|u-v|\in S_j$. By Ramsey's theorem (7.7)
> there exists a monochromatic triangle; that is, there are three vertices $a$,
> $b$ and $c$ such that $ab$, $bc$ and $ca$ have the same colour, say $i$. Assume,
> without loss of generality that $a>b>c$ and write $x=a-b$, $y=b-c$ and
> $z=a-c$. Then $x,y,z\in S_i$ and $x+y=z$.

## In Lean notation

The classical bridge from Ramsey theory to additive number theory.  Schur's
original motivation was Fermat's Last Theorem mod `p`.

The book's motivating example (§7.4, p. 120):

> Consider the partition $(\{1,4,10,13\},\{2,3,11,12\},\{5,6,7,8,9\})$ of the set
> of integers $\{1,2,\ldots,13\}$. We observe that in no subset of the partition
> are there integers $x$, $y$ and $z$ (not necessarily distinct) which satisfy the
> equation $x+y=z$.

⚠ Note "not necessarily distinct" — so `x = y` is allowed, and the Lean statement
correctly does not require distinctness.

⚠ `hpart` says every `k ∈ [1, rₙ]` lies in exactly one part, and `hsub` that no
part escapes the range — together a genuine partition.  But **nothing forces the
parts nonempty**, which is fine (empty parts are harmless).

## Proof plan

1. Colour `Sym2 (Fin rₙ)` by `χ s(u,v) = the i with |u - v| ∈ Sᵢ`, using `hpart`.
   ⚠ Needs the index shift between `Fin rₙ` and `{1, …, rₙ}`.
2. `isRamseyBoundMulti` at `ramseyTriangle n` gives a monochromatic triangle.
3. WLOG `a > b > c`; set `x = a-b`, `y = b-c`, `z = a-c`; all in `Sᵢ` by the
   colouring rule, and `x + y = z` by ℕ arithmetic.

## Status

`sorry`, and **vacuous** pending `ramseyTriangle`'s existence lemma — with
`ramseyTriangle n = 0` the interval `[1, 0]` is empty and the hypotheses hold
trivially for the empty partition.
-/
theorem schur {n : ℕ} (hn : 1 ≤ n) (S : Fin n → Finset ℕ)
    (hpart : ∀ k ∈ Finset.Icc 1 (ramseyTriangle n), ∃! i, k ∈ S i)
    (hsub : ∀ i, S i ⊆ Finset.Icc 1 (ramseyTriangle n)) :
    ∃ i, ∃ x ∈ S i, ∃ y ∈ S i, ∃ z ∈ S i, x + y = z := by
  sorry

/-- The Schur number `sₙ`. (NEEDED-TO-STATE.)
Nonemptiness of the `sInf` set is discharged by Thm 7.10 (`sₙ ≤ rₙ`), itself deferred.

## Book definition (§7.4, p. 120) — verbatim

> Let $s_n$ denote the least integer such that, in any partition of
> $\{1,2,\ldots,s_n\}$ into $n$ subsets, there is a subset which contains a
> solution to (7.19). [...] Also, from theorem 7.10 and exercise 7.2.3 we have the
> upper bound
> $$s_n\le r_n\le[n!\,e]+1$$

## In Lean notation

The exact threshold at which sum-free partitions become impossible.

✅ Unlike most `sInf`s in this chapter, nonemptiness here is supplied by **Theorem
7.10** (`sₙ ≤ rₙ`) — so `schurNumber` is well defined as soon as Schur's theorem
is, without a separate existence lemma.

⚠ But that inherits Theorem 7.10's own vacuity: while `ramseyTriangle n = 0`,
Theorem 7.10 gives nothing and `schurNumber` falls back to `sInf ∅ = 0`.
-/
noncomputable def schurNumber (n : ℕ) : ℕ :=
  sInf {N | ∀ S : Fin n → Finset ℕ,
    (∀ k ∈ Finset.Icc 1 N, ∃! i, k ∈ S i) → (∀ i, S i ⊆ Finset.Icc 1 N) →
      ∃ i, ∃ x ∈ S i, ∃ y ∈ S i, ∃ z ∈ S i, x + y = z}

/-- **Exercise 7.4.1**, third value.  *`s₃ = 14`.*

## Book statement (§7.4, pp. 120–121) — verbatim

> Yet, no matter how we partition $\{1,2,\ldots,14\}$ into three subsets, there
> always exists a subset of the partition which contains a solution to (7.19).

> 7.4.1  Show that $s_1 = 2$, $s_2 = 5$ and $s_3 = 14$.

## In Lean notation

Lower bound from the book's opening partition
`({1,4,10,13}, {2,3,11,12}, {5,6,7,8,9})` of `{1,…,13}`.

Compare `s₃ ≤ r₃ = 17`: the Schur number is strictly below the Ramsey number it
is derived from, so Theorem 7.10's bound is not tight.

## Proof plan

Lower bound: the explicit partition, checking all `x+y=z` within each part.
Upper bound: `3^14` partitions of `{1,…,14}` — **far beyond `decide`**.  Needs
the standard case analysis, which is why the book states it without proof.

## Status

`sorry`.  The upper bound is genuinely hard; of the three values this is the only
one not reachable by finite check.
-/
theorem schurNumber_three : schurNumber 3 = 14 := by sorry

-- Ex 7.4.2(a): 3·sₙ₋₁ ≤ sₙ + 1.
/-- **Exercise 7.4.2(a).**  *`sₙ ≥ 3s_{n-1} - 1`.*

## Book statement (§7.4, p. 121) — verbatim

> 7.4.2  (*a*)  Show that $s_n \geq 3s_{n-1} - 1$.

An exercise, so the book gives no proof.

## In Lean notation

From a sum-free `(n-1)`-partition of `{1,…,s_{n-1}-1}`, build an `n`-partition of
a roughly three-times-longer interval by scaling: keep the old parts tripled, and
give the new `n`-th part the leftover residues.

Stated additively as `3s_{n-1} ≤ sₙ + 1`.

## Proof plan

1. Extract a sum-free `(n-1)`-partition of `{1,…,s_{n-1}-1}` — from `sₙ` being a
   *least* element, i.e. `s_{n-1} - 1` is not in the `sInf` set.
2. Scale: part `i` becomes `{3k, 3k±1 as appropriate}`; the new part collects the
   residues.
3. Verify sum-freeness survives — the bookkeeping the book skips.
4. Conclude `3(s_{n-1}-1) + 1` is not in the set, so `sₙ > 3(s_{n-1}-1)`.

⚠ Step 1 needs the `sInf` set to be **upward closed** for "not below the infimum"
to give a witness — an analogue of `isRamseyBound_mono` for Schur, which is not
stated in this file.

## Status

`sorry`.
-/
theorem schurNumber_recursion {n : ℕ} (hn : 1 ≤ n) :
    3 * schurNumber (n - 1) ≤ schurNumber n + 1 := by
  sorry

-- Ex 7.4.2(b): 27·3^{n−3} + 1 ≤ 2·sₙ.
/-- **Exercise 7.4.2(b).**  *Using (a) and the fact that `s₃ = 14`, show that
`sₙ ≥ ½(27·3^{n-3} + 1)`.*

## Book statement (§7.4, p. 121) — verbatim

> &nbsp;(*b*)  Using (*a*) and the fact that $s_3 = 14$, show that
> $s_n \geq \frac{1}{2}(27(3)^{n-3} + 1)$. (A better lower bound has been obtained
> by Abbott and Moser, 1966.)

An exercise, so the book gives no proof.

## In Lean notation

Iterate `sₙ ≥ 3s_{n-1} - 1` from `s₃ = 14`; solving the linear recurrence gives
`sₙ ≥ (27·3^{n-3} + 1)/2`.

Cleared to `27·3^{n-3} + 1 ≤ 2sₙ`.

Schur numbers grow at least exponentially with ratio `3`; the upper bound
`sₙ ≤ rₙ ≤ ⌊n!e⌋ + 1` grows factorially, and the true rate is unknown.

## Proof plan

Induction on `n` from `n = 3` (`2·14 = 28 = 27·3⁰ + 1` ✓), using
`schurNumber_recursion` at each step and `omega` for the arithmetic.

## Status

`sorry`, depends on `schurNumber_recursion` and `schurNumber_three`.
-/
theorem schurNumber_lower_bound {n : ℕ} (hn : 3 ≤ n) :
    27 * 3 ^ (n - 3) + 1 ≤ 2 * schurNumber n := by
  sorry

/-! # §7.5 — A Geometry Problem -/

/-- The "far pairs" graph: adjacent iff distance exceeds `1/√2`. (NEEDED-TO-STATE; static.)

## Book construction (§7.5, p. 122) — verbatim

> Let $G$ be the graph defined by
> $$V(G) = \{x_1, x_2, \ldots, x_n\}$$
> and
> $$E(G) = \{x_i x_j \mid d(x_i, x_j) > 1/\sqrt{2}\}$$
> where $d(x_i, x_j)$ here denotes the *euclidean* distance between $x_i$ and
> $x_j$.

## In Lean notation

Join two points when they are "far apart", threshold `1/√2`.  The geometry then
forbids `K₄`, which is what lets Turán bound the number of far pairs.

✅ Fully defined, `symm`/`loopless` discharged.

⚠ Same `i ≠ j` guard as `unitDistanceGraph`, and for the same reason: `x` is not
assumed injective.

⚠ The book warns (§7.5, p. 121) that its "diameter" is geometric, not
graph-theoretic:

> It should be noted that this is a purely geometric notion and is quite unrelated
> to the graph-theoretic concepts of diameter and distance.

Rendered as `Metric.diam (Set.range x)`, so no clash with `SimpleGraph.diam`.
-/
def farGraph {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 2)) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ 1 / Real.sqrt 2 < Dist.dist (x i) (x j)
  symm := by rintro i j ⟨h1, h2⟩; exact ⟨h1.symm, by rwa [_root_.dist_comm]⟩
  loopless := by rintro i ⟨h, -⟩; exact h rfl

-- Thm 7.11, half 1 (the [n²/3] bound; rides Turán at r = 3).
/-- **Theorem 7.11**, first half.  *If `{x₁, …, x_n}` is a set of diameter 1 in the
plane, the maximum possible number of pairs of points at distance greater than
`1/√2` is `⌊n²/3⌋`.*

## Book statement (§7.5, p. 122) — verbatim

> **Theorem 7.11** If $\{x_1, x_2, \ldots, x_n\}$ is a set of diameter 1 in the
> plane, the maximum possible number of pairs of points at distance greater than
> $1/\sqrt{2}$ is $[n^2/3]$.

## Book proof (§7.5, p. 122) — verbatim, first half

> We shall show that $G$ cannot contain a $K_4$.
>
> First, note that any four points in the plane must determine an angle of at
> least 90°. For the convex hull of the points is either (a) a line, (b) a
> triangle, or (c) a quadrilateral (see figure 7.5). Clearly, in each case there
> is an angle $x_i x_j x_k$ of at least 90°.
>
> Now look at the three points $x_i$, $x_j$, $x_k$ which determine this angle. Not
> all the distances $d(x_i, x_j)$, $d(x_i, x_k)$ and $d(x_j, x_k)$ can be greater
> than $1/\sqrt{2}$ and less than or equal to 1. For, if $d(x_i, x_j) > 1/\sqrt{2}$
> and $d(x_j, x_k) > 1/\sqrt{2}$, then $d(x_i, x_k) > 1$. Since the set
> $\{x_1, x_2, \ldots, x_n\}$ is assumed to have diameter 1, it follows that, of
> any four points in $G$, at least one pair cannot be joined by an edge, and hence
> that $G$ cannot contain a $K_4$. By Turán's theorem (7.9)
> $$\varepsilon(G) \le \varepsilon(T_{3,n}) = [n^2/3]$$

## In Lean notation

Two genuinely geometric inputs, neither in Mathlib:
1. **Any four points in the plane determine an angle `≥ 90°`** — a convex-hull
   case analysis (line / triangle / quadrilateral).
2. **The law of cosines consequence**: an angle `≥ 90°` at `xⱼ` with both
   adjacent sides `> 1/√2` forces the opposite side `> 1`.

Given those, `farGraph` is `K₄`-free and `turan_edge_bound` at `m = 3` finishes.

## Proof plan

1. Prove (2) from `EuclideanSpace`'s inner-product structure — `dist_sq` expansion
   plus `inner ≤ 0` for an obtuse angle.  The more tractable of the two.
2. Prove (1) — the convex-hull trichotomy.  ⚠ Substantial plane geometry;
   Mathlib's `convexHull` API exists but this specific statement does not.
3. `CliqueFree 4` for `farGraph`, then `turan_edge_bound`.
4. Evaluate `#(turanGraph n 3).edgeFinset = ⌊n²/3⌋`.

## Book illustration (§7.5, pp. 121–122)

Six points on a regular hexagon give only nine far pairs; a better configuration
achieves twelve `= ⌊36/3⌋`.

## Status

`sorry`.  The graph theory is a one-liner off Turán; the geometry at steps 1–2 is
the whole difficulty.
-/
theorem card_farGraph_le
    {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 2))
    [DecidableRel (farGraph x).Adj]
    (hdiam : Metric.diam (Set.range x) = 1) :
    #(farGraph x).edgeFinset ≤ n ^ 2 / 3 := by
  sorry

-- Thm 7.11, half 2 (the "Moreover" construction; harder than half 1).
/-- **Theorem 7.11**, second half.  *Moreover, for each `n`, there is a set
`{x₁, …, x_n}` of diameter 1 with exactly `⌊n²/3⌋` pairs of points at distance
greater than `1/√2`.*

## Book statement (§7.5, p. 122) — verbatim

> Moreover, for each $n$, there is a set $\{x_1, x_2, \ldots, x_n\}$ of diameter 1
> with exactly $[n^2/3]$ pairs of points at distance greater than $1/\sqrt{2}$.

## Book proof (§7.5, p. 123) — verbatim

> One can construct a set $\{x_1, x_2, \ldots, x_n\}$ of diameter 1 in which
> exactly $[n^2/3]$ pairs of points are at distance greater than $1/\sqrt{2}$ as
> follows. Choose $r$ such that $0 < r < (1 - 1/\sqrt{2})/4$, and draw three
> circles of radius $r$ whose centres are at a distance of $1 - 2r$ from one
> another (figure 7.6). Place $x_1, \ldots, x_{[n/3]}$ in one circle,
> $x_{[n/3]+1}, \ldots, x_{[2n/3]}$ in another, and $x_{[2n/3]+1}, \ldots, x_n$ in
> the third, in such a way that $d(x_1, x_n) = 1$. This set clearly has diameter 1.
> Also, $d(x_i, x_j) > 1/\sqrt{2}$ if and only if $x_i$ and $x_j$ are in different
> circles, and so there are exactly $[n^2/3]$ pairs $(x_i, x_j)$ for which
> $d(x_i, x_j) > 1/\sqrt{2}$.

## In Lean notation

The far-pairs graph of this configuration is *exactly* the balanced complete
tripartite `T_{3,n}`, with `⌊n²/3⌋` edges — so the Turán bound is attained and
the geometric optimum is realised by the graph-theoretic extremal configuration.

## Proof plan

1. Fix `r` (any concrete choice below `(1 - 1/√2)/4` works, e.g. `1/100`) and
   three centres at mutual distance `1 - 2r`.
2. Place points; the book's "in such a way that `d(x₁, xₙ) = 1`" is what pins the
   diameter to exactly `1` rather than merely `≤ 1`.  ⚠ That placement is
   asserted, not constructed — supplying explicit coordinates is the formaliser's
   job.
3. Same-circle distances `≤ 2r < 1/√2`; different-circle distances
   `≥ (1-2r) - 2r = 1 - 4r > 1/√2`.  Both from the triangle inequality, and both
   are where the bound on `r` is used.
4. Edge count `= ⌊n²/3⌋` by the tripartite structure.

## Status

`sorry`.  More tractable than the first half — the estimates at step 3 are
elementary — but needs explicit coordinates the book does not give.
-/
theorem exists_farGraph_card_eq (n : ℕ) :
    ∃ (x : Fin n → EuclideanSpace ℝ (Fin 2)) (_ : DecidableRel (farGraph x).Adj),
      Metric.diam (Set.range x) = 1 ∧ #(farGraph x).edgeFinset = n ^ 2 / 3 := by
  sorry

-- Ex 7.5.1(a)* (Pannwitz): at most n unit-distance pairs among n diameter-1 points.
/-- **Exercise 7.5.1(a)*** (Pannwitz).  *Let `{x₁, …, x_n}` be a set of diameter 1
in the plane.  The maximum possible number of pairs of points at distance 1 is
`n`.*

## Book statement (§7.5, p. 123) — verbatim

> 7.5.1\* Let $\{x_1, x_2, \ldots, x_n\}$ be a set of diameter 1 in the plane.
> &nbsp;($a$) Show that the maximum possible number of pairs of points at distance
> 1 is $n$.

A starred exercise, so the book gives no proof.

## In Lean notation

In a diameter-1 set, a pair at distance exactly `1` is a *diameter pair*.  The
key geometric fact: two diameter pairs must cross or share a point — if `ab` and
`cd` were disjoint diameters, one of the four cross distances would exceed `1`.

That crossing property forces the diameter graph to have `≤ n` edges.

Contrast exercise 7.3.4(c), where without the diameter restriction the bound is
of order `n^{3/2}`; bounding the diameter collapses it to **linear**.

## Proof plan

1. **The geometric input**: two disjoint diameter pairs are impossible — from the
   triangle inequality plus the diameter-1 constraint.  Not in Mathlib.
2. Hence the diameter graph has no two independent edges *that do not cross*,
   which combinatorially forces `ε ≤ n`.  ⚠ Step 2 is not a standard graph
   lemma — "every two edges cross" bounds the edge count only via the planarity
   of the crossing structure, and the clean route is the classical Sylvester-style
   argument rather than anything graph-theoretic.

## Status

`sorry`.  Both steps are genuine plane geometry; this is the least
graph-theoretic result in the chapter.
-/
theorem card_unitDistanceGraph_le_of_diam_one
    {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 2))
    [DecidableRel (unitDistanceGraph x).Adj]
    (hdiam : Metric.diam (Set.range x) = 1) :
    #(unitDistanceGraph x).edgeFinset ≤ n := by
  sorry

/-- The radio-range graph: adjacent iff within `range`. (NEEDED-TO-STATE; static.)

## Book context (exercise 7.5.2, p. 123)

The graph is the formaliser's construction; the book states the exercise purely
in terms of cars and radios — see `police_cars` below for the verbatim text.

## In Lean notation

Join two cars when within `range`.  Turns a communications question into a degree
question: "car `i` reaches `k` others" is "vertex `i` has degree `k`".

✅ Fully defined.

⚠ Uses `≤ range`, not `<` — so cars at exactly the limit *can* communicate.  The
exercise does not say which, and the conclusion is unaffected.
-/
def radioGraph {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 2)) (range : ℝ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ Dist.dist (x i) (x j) ≤ range
  symm := by rintro i j ⟨h1, h2⟩; exact ⟨h1.symm, by rwa [_root_.dist_comm]⟩
  loopless := by rintro i ⟨h, -⟩; exact h rfl

/-! ### Book content for items not stated above

*Exercise 7.2.2.*  Prove theorem 7.7 and corollary 7.7 — the book leaves the
multicolour recursion and its multinomial consequence as an exercise, noting they
*can be proved in a similar manner* to theorem 7.4 and theorem 7.5.

*Exercise 7.3.2.*  A bridge club allows four members to play together only if no
two have previously partnered.  Fourteen members turn up, each having previously
partnered five others; three games are played and then the club rule halts
proceedings.  A new member, unknown to all, then arrives — show at least one more
game can be played.  (A counting argument in the "previously partnered" graph,
much like exercise 7.3.1.) -/

end SimpleGraph
