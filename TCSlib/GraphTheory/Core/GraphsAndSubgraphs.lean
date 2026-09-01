import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Data.Nat.Choose.Basic

/-!
# Bondy & Murty, *Graph Theory with Applications* — Chapter 1: Graphs and Subgraphs

Sorry-skeleton extracted from `book copy/01_chapter-1-graphs-and-subgraphs.md`.

This is a **scaffold** for sorry-driven development: every proof body is `sorry`.
Chapter 1 is elementary and almost every notion already lives in Mathlib, so we
*reference* Mathlib definitions (`SimpleGraph`, `≃g`, `adjMatrix`, `incMatrix`,
`Subgraph`, `degree`, `Walk`, `IsCycle`, `girth`, `Colorable 2`, …) rather than
redefining them.  Book theorems/corollaries and the meatier exercises are stated
as `:= by sorry` stubs; where Mathlib already proves the result, a
`-- Mathlib: <name>` comment points at the lemma that can close the stub.

Carrier throughout: `SimpleGraph V`.  Note Bondy & Murty's "graph" allows loops
and parallel edges; Mathlib's `SimpleGraph` is loopless and simple, which is the
setting for "much of graph theory" (§1.1) and for every simple-graph statement
in the chapter.

## How each declaration is annotated

Every docstring below has a fixed shape, so the book's mathematics stays separable
from this file's formalisation choices:

1. **The book's own statement** (theorem/exercise) or **definition** (`def`), quoted
   verbatim from Bondy & Murty, LaTeX transcribed into Lean-style backticks.
2. **Book proof** — B&M's printed proof, verbatim.  Chapter 1 prints proofs only for
   theorems 1.1 and 1.2 and their corollary; everything else is an exercise, and
   says so rather than being filled in with a reconstruction.
3. Then, depending on the state of the declaration:
   * **Proof** — for the 19 declarations already *proved* here: what the Lean proof
     actually does, and which Mathlib lemma carries it where one does.
   * **Skeleton** — for the 22 still stubbed: an abstract numbered plan keyed to the
     Lean statement, naming intermediate facts, not committing to tactics.
4. **Reading** — what the result means and how it sits in the chapter.
5. **Formalisation** — only where the Lean statement departs from the book's.

⚠ Unlike chapters 9–12 of this repo, **no definition in this file has a `sorry`
body** — the one local definition (`hypercube`) is honest, and everything else is
Mathlib's.  So the statements here mean what they say.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## §1.1 Graphs and simple graphs

`SimpleGraph V` (Mathlib) is a loopless, simple graph on `V`.  We write `ν = Fintype.card V`
for the number of vertices and `ε = G.edgeFinset.card` for the number of edges.
A *loop* is an edge with equal ends and a *link* an edge with distinct ends; a
*simple* graph has neither — exactly `SimpleGraph`.  `completeGraph V = (⊤ : SimpleGraph V)`
and an *empty graph* is `(⊥ : SimpleGraph V)`. -/

/-! ### Book definitions, §1.1 (Graphs and simple graphs)

*Graph.*  An ordered triple `(V(G), E(G), ψ_G)`: a nonempty vertex set, a
disjoint edge set, and an incidence function sending each edge to an unordered
pair of vertices.  Graphs are drawn as diagrams — a point per vertex, a line per
edge joining the points representing its ends — but the drawing carries no
information beyond the incidence relation, so the same graph has many diagrams.

*Planar.*  A graph is planar when it has some diagram whose edges meet only at
their ends.  (Chapter 9 develops this; chapter 1 only names it.)

*Loop, link, simple.*  A loop is an edge whose two ends coincide; a link is an
edge with distinct ends.  A simple graph has no loops, and no two of its links
join the same pair of vertices.  Much of graph theory concerns simple graphs,
and Mathlib's `SimpleGraph` is precisely this notion.

*Finite, trivial.*  A graph is finite when both its vertex set and edge set are
finite; "graph" in the book always means "finite graph".  A graph with just one
vertex is trivial, all others nontrivial.

*Order and size.*  `ν(G)` is the number of vertices, `ε(G)` the number of
edges. -/

/-! ## §1.2 Graph isomorphism

Mathlib: an isomorphism is `G ≃g H` (`SimpleGraph.Iso`, an adjacency-preserving
equivalence), an embedding is `G ↪g H` (`SimpleGraph.Embedding`).  The complete
graph `Kₙ` is `completeGraph (Fin n) = ⊤`; the complete bipartite graph `K_{m,n}`
is `completeBipartiteGraph (Fin m) (Fin n)`; a graph is *bipartite* iff
`G.Colorable 2` (Mathlib abbrev `SimpleGraph.IsBipartite`). -/

/-! ### Book definitions, §1.2 (Graph isomorphism)

*Identical graphs.*  `G = H` means `V(G) = V(H)`, `E(G) = E(H)` and
`ψ_G = ψ_H` — literally the same vertex set, edge set and incidence function.

*Isomorphic graphs.*  `G ≅ H` means there are bijections `θ : V(G) → V(H)` and
`φ : E(G) → E(H)` such that `ψ_G(e) = uv` if and only if
`ψ_H(φ(e)) = θ(u)θ(v)`; the pair `(θ, φ)` is an **isomorphism**.  Isomorphic
graphs have the same structure and differ only in the names of their vertices
and edges, so an unlabelled graph represents an equivalence class of isomorphic
graphs.  For simple graphs the edge bijection `φ` is redundant: a vertex
bijection preserving adjacency suffices (exercise 1.2.5).

*Complete graph.*  A simple graph in which each pair of distinct vertices is
joined by an edge.  Up to isomorphism there is exactly one on `n` vertices,
denoted `Kₙ`.

*Empty graph.*  A graph with no edges.

*Bipartite graph.*  One whose vertex set can be partitioned into two subsets `X`
and `Y` so that every edge has one end in `X` and one end in `Y`; the partition
`(X, Y)` is a **bipartition**.

*Complete bipartite graph.*  A simple bipartite graph with bipartition `(X, Y)`
in which every vertex of `X` is joined to every vertex of `Y`.  With `|X| = m`
and `|Y| = n` it is denoted `K_{m,n}`.

*Complement.*  The complement `Gᶜ` of a simple graph `G` is the simple graph on
the same vertex set in which two vertices are adjacent exactly when they are
*not* adjacent in `G`.  `G` is **self-complementary** when `G ≅ Gᶜ`. -/

-- Ex 1.2.5: two simple graphs are isomorphic iff some vertex bijection preserves adjacency.
/-- **Exercise 1.2.5.**  *Two simple graphs `G` and `H` are isomorphic if and only
if there is a bijection `θ : V(G) → V(H)` such that `uv ∈ E(G)` if and only if
`θ(u)θ(v) ∈ E(H)`.*

**Book proof.**  None — an exercise.

**Proof.**  Both directions unfold `SimpleGraph.Iso`: forwards, take `f.toEquiv` and
`f.map_rel_iff`; backwards, package `θ` with the adjacency equivalence.  Two lines
each — the content is entirely in the *statement*, which asserts that Mathlib's
definition of `≃g` is the book's.

**Reading.**  B&M's general isomorphism needs two bijections, one on vertices and one
on edges, respecting incidence.  For *simple* graphs the edge bijection carries no
information — at most one edge joins any pair — so an adjacency-preserving vertex
bijection already induces it.  This is precisely why Mathlib can define `G ≃g H` as
an equivalence of vertex types with `G.Adj u v ↔ H.Adj (θ u) (θ v)`, and this
exercise is the justification for using it throughout the file. -/
theorem nonempty_iso_iff {W : Type*} (H : SimpleGraph W) :
    Nonempty (G ≃g H) ↔ ∃ θ : V ≃ W, ∀ u v, G.Adj u v ↔ H.Adj (θ u) (θ v) := by
  constructor
  · rintro ⟨f⟩
    exact ⟨f.toEquiv, fun u v => f.map_rel_iff.symm⟩
  · rintro ⟨θ, hθ⟩
    exact ⟨⟨θ, fun {a b} => (hθ a b).symm⟩⟩

-- Ex 1.2.7: a simple graph is complete iff `ε = C(ν, 2)`.
/-- **Exercise 1.2.7.**  *Let `G` be simple.  Then `ε = C(ν, 2)` if and only if
`G` is complete.*

**Book proof.**  None — an exercise.

**Proof.**  Forwards: `G.edgeFinset ⊆ (⊤).edgeFinset` by `edgeFinset_mono`, and the
cardinalities agree by hypothesis plus
`card_edgeFinset_top_eq_card_choose_two`, so `Finset.eq_of_subset_of_card_le` and
`edgeFinset_inj` give `G = ⊤`.  Backwards: `card_edgeFinset_top_eq_card_choose_two`
directly.  ⚠ The `convert … using 3` in the backwards branch is there because
`rintro rfl` leaves the section's `DecidableRel G.Adj` instance behind, which must be
reconciled with the one `⊤` carries — a recurring instance-mismatch pattern worth
recognising.

**Reading.**  Exercise 1.1.3 gives `ε ≤ C(ν,2)`; equality means the injection from
edges to pairs is *onto*, i.e. every pair carries an edge — the definition of
complete.

**Formalisation.**  "Complete" is `G = ⊤`, the top of the lattice of simple graphs
on `V`. -/
theorem edgeCard_eq_choose_two_iff_top :
    G.edgeFinset.card = (Fintype.card V).choose 2 ↔ G = ⊤ := by
  constructor
  · -- equality forces the edge set to exhaust every pair, i.e. `G = ⊤`
    intro h
    have hsub : G.edgeFinset ⊆ (⊤ : SimpleGraph V).edgeFinset := edgeFinset_mono le_top
    have htop : ((⊤ : SimpleGraph V).edgeFinset).card = (Fintype.card V).choose 2 :=
      card_edgeFinset_top_eq_card_choose_two
    have hcard : ((⊤ : SimpleGraph V).edgeFinset).card ≤ G.edgeFinset.card := by
      rw [htop, h]
    exact edgeFinset_inj.mp (Finset.eq_of_subset_of_card_le hsub hcard)
  · -- `G = ⊤` realises every pair.  (`rintro rfl` leaves the section's
    -- `DecidableRel G.Adj` instance behind, so match it up with `Subsingleton.elim`.)
    rintro rfl
    convert card_edgeFinset_top_eq_card_choose_two (V := V) using 3

-- Ex 1.2.8(a): `ε(K_{m,n}) = mn`.
/-- **Exercise 1.2.8(a).**  *`ε(K_{m,n}) = mn`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `(completeBipartiteGraph (Fin m) (Fin n)).edgeFinset.card = m * n`).
1. **Exhibit the bijection** `edgeSet ≃ Fin m × Fin n`.  Forwards: an edge of
   `completeBipartiteGraph` is a `Sym2` whose two ends lie on opposite sides, so
   `Sym2.lift` extracts the ordered pair (well defined, since the unordered pair has
   exactly one member on each side).  Backwards: `(i, j) ↦ s(inl i, inr j)`.
2. `Fintype.card_congr` on step 1, then `Fintype.card_prod`.
3. Reconcile `Nat.card`/`Fintype.card`/`edgeFinset.card` — `card_edgeFinset` bridges
   the last two.

**Reading.**  `K_{m,n}` contains exactly one edge for each choice of a vertex in `X`
and one in `Y`, so edges biject with `X × Y`.

**Formalisation.**  The carrier is `Fin m ⊕ Fin n`, so "opposite sides" is a `Sum`
case split; step 1's well-definedness is the only fiddly point. -/
theorem completeBipartite_edgeCard (m n : ℕ)
    [DecidableRel (completeBipartiteGraph (Fin m) (Fin n)).Adj] :
    (completeBipartiteGraph (Fin m) (Fin n)).edgeFinset.card = m * n := by
  sorry

-- Ex 1.2.8(b): a simple bipartite graph satisfies `ε ≤ ν²/4` (stated `4ε ≤ ν²`).
/-- **Exercise 1.2.8(b).**  *If `G` is simple and bipartite, then `ε ≤ ν²/4`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `4 * ε ≤ ν ^ 2`, given `h : G.Colorable 2`).
1. **Extract the bipartition.**  `h` gives `c : G.Coloring (Fin 2)`; set
   `X := c ⁻¹' {0}`, `Y := c ⁻¹' {1}`, with `|X| + |Y| = ν`.
2. **`ε ≤ |X| · |Y|`.**  Every edge has one end in each class (properness), and
   distinct edges give distinct pairs (simplicity), so `edgeFinset` injects into
   `X ×ˢ Y`.
3. **AM–GM in ℕ:** `4 * |X| * |Y| ≤ (|X| + |Y|)^2`, since the difference is
   `(|X| - |Y|)^2 ≥ 0`.  ⚠ In ℕ prove it as `4*a*b + (a-b)^2 = (a+b)^2` only after
   case-splitting on `a ≤ b`, or move to `ℤ` and cast back — ℕ-subtraction
   truncates.
4. Chain: `4ε ≤ 4|X||Y| ≤ ν²`.

**Reading.**  `mn` with fixed sum `ν` is largest when the parts are equal, giving
`ν²/4`; the bound is attained by `K_{ν/2,ν/2}`.

**Formalisation.**  Stated in the cleared form `4ε ≤ ν²` to stay in ℕ, and
bipartiteness as `Colorable 2` — Mathlib's `IsBipartite` is an abbreviation for
exactly that. -/
theorem bipartite_edgeCard_le (h : G.Colorable 2) :
    4 * G.edgeFinset.card ≤ (Fintype.card V) ^ 2 := by
  sorry

/-- Ex 1.2.10: the `k`-cube — vertices are `k`-bit strings, adjacent iff they differ
in exactly one coordinate.  (Mathlib has no named hypercube graph; we build it.)

**Book definition (exercise 1.2.10).**  *The `k`-cube is the graph whose vertices
are the ordered `k`-tuples of `0`s and `1`s, two vertices being joined if and
only if they differ in exactly one coordinate.*

**Reading.**  Each vertex is a binary string of length `k`, equivalently a corner of a
`k`-dimensional cube; two corners are joined when their descriptions agree everywhere
but one position.  For `k = 3` this is literally the corners and edges of an ordinary
cube — the book's figure 1.4b.

**Formalisation.**  Mathlib has no named hypercube graph, so this is built here.
Tuples are `Fin k → Bool`; "differ in exactly one coordinate" is `∃! i, x i ≠ y i`.
`SimpleGraph.fromRel` symmetrises the relation and removes the diagonal, which is
what makes the result a `SimpleGraph` without a separate looplessness proof — at the
cost that `Adj` unfolds to `x ≠ y ∧ (R x y ∨ R y x)`, as the `hypercube_bipartite`
proof has to unpack. -/
def hypercube (k : ℕ) : SimpleGraph (Fin k → Bool) :=
  SimpleGraph.fromRel (fun x y => ∃! i, x i ≠ y i)

-- Ex 1.2.10: the `k`-cube has `k · 2^(k-1)` edges.
/-- **Exercise 1.2.10 (edge count).**  *The `k`-cube has `k · 2^(k-1)` edges.*

**Book proof.**  None — an exercise.

**Skeleton** (for `(hypercube k).edgeFinset.card = k * 2 ^ (k-1)`).
1. **`hypercube k` is `k`-regular.**  The neighbours of `x` are exactly the `k`
   tuples `Function.update x i (!x i)`, one per coordinate, and these are distinct.
   So `degree x = k`.
2. **Handshake** (theorem 1.1): `2ε = ∑ x, degree x = k * 2^k`.
3. Divide: `ε = k * 2^(k-1)`.  ⚠ In ℕ, do this as `2 * ε = 2 * (k * 2^(k-1))` using
   `2^k = 2 * 2^(k-1)` and cancel — but that identity needs `k ≥ 1`, so dispatch
   `k = 0` separately (the `0`-cube is a single vertex with no edges, and
   `0 * 2^(0-1) = 0` ✓).

**Reading.**  Every vertex has degree `k`, one neighbour per coordinate flip.

**Formalisation.**  ⚠ `k - 1` is ℕ-subtraction; the `k = 0` case is where it bites,
and it happens to come out right, but only by accident of `0 * _ = 0`. -/
theorem hypercube_edgeCard (k : ℕ) [DecidableRel (hypercube k).Adj] :
    (hypercube k).edgeFinset.card = k * 2 ^ (k - 1) := by
  sorry

-- Ex 1.2.10: the `k`-cube is bipartite.
/-- **Exercise 1.2.10 (bipartiteness).**  *The `k`-cube is bipartite.*

**Book proof.**  None — an exercise.

**Proof.**  Colour `x` by `∑ i, g (x i) : ZMod 2`, the parity of its number of `1`s.
For an edge, `fromRel_adj` yields the unique differing coordinate `i₀`; every other
coordinate agrees, so the two sums differ exactly in the `i₀` term, and
`add_right_cancel` reduces properness to `g (x i₀) ≠ g (y i₀)` — closed by
`cases x i₀ <;> cases y i₀ <;> simp`.  The `∃!` has to be extracted from the
symmetrised `fromRel` disjunction first, which is the only fiddly step.

**Reading.**  Split the tuples by the parity of their number of `1`s; an edge flips
exactly one entry and so changes that parity, making every edge cross between the
classes.

**Formalisation.**  Bipartiteness as `Colorable 2`, with `ZMod 2` as the palette and
`simpa` bridging to `Fin 2`. -/
theorem hypercube_bipartite (k : ℕ) : (hypercube k).Colorable 2 := by
  classical
  -- Colour a vertex by the parity of the number of `1`s it contains.
  set g : Bool → ZMod 2 := fun b => if b then 1 else 0 with hg
  have hcol : (hypercube k).Coloring (ZMod 2) := by
    refine SimpleGraph.Coloring.mk (fun x => ∑ i, g (x i)) ?_
    intro x y hadj
    simp only [hypercube, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, hr⟩ := hadj
    -- the two ends differ in exactly one coordinate `i₀`
    obtain ⟨i₀, hi₀, huniq⟩ : ∃! i, x i ≠ y i := by
      rcases hr with h | h
      · exact h
      · obtain ⟨i, hi, hu⟩ := h
        exact ⟨i, hi.symm, fun j hj => hu j hj.symm⟩
    -- every other coordinate agrees, so the tails of the two sums coincide
    have hrest : ∀ i ∈ Finset.univ.erase i₀, g (x i) = g (y i) := by
      intro i hi
      have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
      have : x i = y i := by
        by_contra hxy
        exact hne (huniq i hxy)
      rw [this]
    show (∑ i, g (x i)) ≠ (∑ i, g (y i))
    rw [← Finset.add_sum_erase _ (fun i => g (x i)) (Finset.mem_univ i₀),
        ← Finset.add_sum_erase _ (fun i => g (y i)) (Finset.mem_univ i₀),
        Finset.sum_congr rfl hrest]
    -- crossing the one differing coordinate flips the parity
    intro hcontra
    have hxy : g (x i₀) = g (y i₀) := add_right_cancel hcontra
    revert hxy hi₀
    cases x i₀ <;> cases y i₀ <;> simp [hg]
  simpa using hcol.colorable

-- Ex 1.2.11(b): a self-complementary simple graph has `ν ≡ 0` or `1 (mod 4)`.
/-- **Exercise 1.2.11(b).**  *If `G` is self-complementary, then `ν ≡ 0` or
`1 (mod 4)`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `ν % 4 = 0 ∨ ν % 4 = 1`).
1. **`ε(G) + ε(Gᶜ) = C(ν,2)`** — every pair of distinct vertices carries an edge in
   exactly one of the two.
2. **`ε(G) = ε(Gᶜ)`** from `f` by exercise 1.2.2(a).
3. Combine: `2 ε(G) = C(ν,2)`, i.e. `4 ε(G) = ν(ν-1)` after clearing the `/2` in
   `C(ν,2)` (use `Nat.choose_two_right` in its doubled form to avoid ℕ-division).
4. **Arithmetic.**  `4 ∣ ν(ν-1)` with `ν`, `ν-1` consecutive, so not both even —
   hence `4 ∣ ν` or `4 ∣ ν-1`.  `omega` after `interval_cases` on `ν % 4`.

**Reading.**  Self-complementary means `G ≅ Gᶜ`, so `G` has exactly half of all
possible edges — which forces `ν ≡ 0` or `1 (mod 4)`.  The smallest examples are the
path `P₄` (`ν = 4`) and the cycle `C₅` (`ν = 5`). -/
theorem selfComplementary_card_mod_four (f : G ≃g Gᶜ) :
    Fintype.card V % 4 = 0 ∨ Fintype.card V % 4 = 1 := by
  sorry

-- DROPPED: Ex 1.2.9 (Turán graph `T_{m,n}` edge count / extremality) and Ex 1.2.12–13
-- (automorphism group `Γ(G)`, vertex/edge-transitivity) — no single clean signature;
-- these are a family of computations rather than one statable theorem.

/-! ### Book definitions for the dropped items, §1.2

*`k`-partite graph* (exercise 1.2.9).  One whose vertex set can be partitioned
into `k` subsets so that no edge has both ends in any one subset.  A **complete
`k`-partite graph** is simple and joins each vertex to every vertex outside its
own subset.  `T_{m,n}` denotes the complete `m`-partite graph on `n` vertices in
which each part has either `⌊n/m⌋` or `⌈n/m⌉` vertices; it maximises the edge
count among complete `m`-partite graphs on `n` vertices.

*Automorphism* (exercise 1.2.12).  An isomorphism of a graph onto itself.  For a
simple graph this is a permutation of `V` preserving adjacency; these
permutations form a group `Γ(G)` under composition, the **automorphism group**,
and `Γ(G) = Γ(Gᶜ)`.

*Vertex- and edge-transitive* (exercise 1.2.13).  `G` is vertex-transitive when
some automorphism carries any given vertex to any other, and edge-transitive
when some automorphism carries any given edge to any other. -/

/-! ## §1.3 The incidence and adjacency matrices

Mathlib: `G.adjMatrix α : Matrix V V α` (`aᵢⱼ = 1` iff `vᵢ ~ vⱼ`) and
`G.incMatrix R : Matrix V (Sym2 V) R` (`mᵥₑ = 1` iff `v` incident with `e`).
For simple graphs these have 0/1 entries. -/

/-! ### Book definitions, §1.3 (Incidence and adjacency matrices)

*Incidence matrix.*  With the vertices of `G` listed as `v₁, …, v_ν` and the
edges as `e₁, …, e_ε`, the incidence matrix is the `ν × ε` matrix `M(G) = [m_ij]`
where `m_ij` is the number of times (`0`, `1` or `2`) that `v_i` and `e_j` are
incident.  The entry is `2` exactly when `e_j` is a loop at `v_i`.  The incidence
matrix is just another way of specifying the graph.

*Adjacency matrix.*  The `ν × ν` matrix `A(G) = [a_ij]` in which `a_ij` is the
number of edges joining `v_i` and `v_j`.  For a simple graph every entry is `0`
or `1` and the diagonal is zero.  The adjacency matrix is generally much smaller
than the incidence matrix, and is the usual way graphs are stored in
computers. -/

/-! ## §1.4 Subgraphs

Mathlib: `H ≤ G` is the subgraph relation on `SimpleGraph V`; the richer
`SimpleGraph.Subgraph G` bundles a vertex set with an edge set.
`G'.IsSpanning` (verts = univ), `G'.IsInduced`, and `G.induce (s : Set V)` (the
induced subgraph `G[s]`) are all in Mathlib. -/

/-! ### Book definitions, §1.4 (Subgraphs)

*Subgraph.*  `H ⊆ G` when `V(H) ⊆ V(G)`, `E(H) ⊆ E(G)` and `ψ_H` is the
restriction of `ψ_G` to `E(H)`.  If moreover `H ≠ G` then `H` is a **proper**
subgraph, and `G` is a **supergraph** of `H`.

*Spanning subgraph.*  A subgraph `H` with `V(H) = V(G)` — it keeps every vertex
and only discards edges.

*Underlying simple graph.*  Obtained from `G` by deleting all loops and, for each
adjacent pair, all but one of the links joining them; it is a simple spanning
subgraph of `G`.

*Induced subgraph `G[V']`.*  For a nonempty `V' ⊆ V`, the subgraph with vertex
set `V'` whose edges are exactly those edges of `G` having *both* ends in `V'`.
`G - V'` abbreviates `G[V \ V']`, the graph obtained by deleting the vertices in
`V'` together with their incident edges; `G - v` means `G - {v}`.

*Edge-induced subgraph `G[E']`.*  For a nonempty `E' ⊆ E`, the subgraph whose
edges are `E'` and whose vertices are the ends of those edges.  `G - E'` is the
spanning subgraph with edge set `E \ E'`, and `G + E'` adjoins the edges `E'`;
`G - e` and `G + e` abbreviate the singleton cases.

*Disjoint, union, intersection.*  Two subgraphs are **disjoint** when they share
no vertex, **edge-disjoint** when they share no edge.  Their **union**
`G₁ ∪ G₂` has vertex set `V(G₁) ∪ V(G₂)` and edge set `E(G₁) ∪ E(G₂)`; their
**intersection** is defined analogously and requires a common vertex. -/

-- Ex 1.4.2(a): an induced subgraph of a complete graph is complete.
/-- **Exercise 1.4.2(a).**  *Every induced subgraph of a complete graph is
complete.*

**Book proof.**  None — an exercise.

**Proof.**  `ext a b; simp [Subtype.coe_injective.ne_iff]` — adjacency in the induced
subgraph unfolds to distinctness of the underlying vertices, which `Subtype`
injectivity transports to distinctness in the subtype.

**Reading.**  `G[V']` keeps `V'` and *all* edges of `G` with both ends there.  If `G`
is complete, every pair inside `V'` is joined and every such edge is retained — so
`G[V']` is complete. -/
theorem induce_completeGraph (s : Set V) :
    (⊤ : SimpleGraph V).induce s = ⊤ := by
  ext a b
  simp [Subtype.coe_injective.ne_iff]

-- Ex 1.4.2(b): every subgraph of a bipartite graph is bipartite.
-- Mathlib: SimpleGraph.Colorable.mono_left
/-- **Exercise 1.4.2(b).**  *Every subgraph of a bipartite graph is bipartite.*

**Book proof.**  None — an exercise.

**Proof.**  `hG.mono_left hle`, Mathlib — a proper colouring of `G` restricts to any
subgraph.

**Reading.**  Every edge of `H` is an edge of `G`, so the very same bipartition still
has every edge crossing: deleting vertices and edges can never create an edge inside
a part.

**Formalisation.**  Stated for `H ≤ G` on the *same* carrier, which is the
spanning-subgraph case.  B&M's "subgraph" also allows dropping vertices; that case is
`induce_bipartite` and the two together are `subgraph_induce_bipartite`, both below. -/
theorem subgraph_bipartite {H : SimpleGraph V} (hle : H ≤ G) (hG : G.Colorable 2) :
    H.Colorable 2 :=
  hG.mono_left hle

-- Ex 1.4.2(b), induced case: every *induced* subgraph of a bipartite graph is bipartite.
-- Mathlib: SimpleGraph.Colorable.of_embedding, SimpleGraph.Embedding.induce
/-- **Exercise 1.4.2(b)**, induced case.  *Every induced subgraph of a bipartite graph
is bipartite.*

**Proof.**  `Colorable.of_embedding (Embedding.induce s) hG` — the inclusion
`G[s] ↪g G` pulls a proper 2-colouring of `G` back to `G[s]`.

**Reading.**  `subgraph_bipartite` covers B&M's *spanning* subgraphs (same vertex set,
fewer edges); this covers the other half of what B&M call a subgraph — throwing
vertices away.  Restricting a bipartition to a vertex subset still leaves every
surviving edge crossing. -/
theorem induce_bipartite (s : Set V) (hG : G.Colorable 2) :
    (G.induce s).Colorable 2 :=
  Colorable.of_embedding (Embedding.induce s) hG

-- Ex 1.4.2(b), general form: B&M's "subgraph" = drop edges *and* vertices.
/-- **Exercise 1.4.2(b)**, general form.  *Every subgraph of a bipartite graph is
bipartite*, with "subgraph" read as B&M read it: drop edges **and** vertices.

**Proof.**  Compose the two special cases — `hG.mono_left hle` restricts the colouring
to `H`, then `Embedding.induce s` restricts it to `s`.

**Reading.**  This is the exercise as the book states it; `subgraph_bipartite`
(edges only) and `induce_bipartite` (vertices only) are the two halves, and either
alone is what a Lean transcription tends to produce.  ⚠ Nothing in the proof uses
`2` specifically; the identical two lines give the `Colorable k` statement for any
`k`, should a general version be wanted. -/
theorem subgraph_induce_bipartite {H : SimpleGraph V} (hle : H ≤ G) (s : Set V)
    (hG : G.Colorable 2) :
    (H.induce s).Colorable 2 :=
  Colorable.of_embedding (Embedding.induce s) (hG.mono_left hle)

/-! ## §1.5 Vertex degrees

Mathlib: `G.degree v`, `G.minDegree` (`δ`), `G.maxDegree` (`Δ`),
`G.IsRegularOfDegree k` (`k`-regular). -/

/-! ### Book definitions, §1.5 (Vertex degrees)

*Degree.*  The degree `d_G(v)` of a vertex `v` is the number of edges of `G`
incident with `v`, **each loop counting as two edges**.  (In a `SimpleGraph`
there are no loops, so this is just the number of neighbours of `v`.)

*Minimum and maximum degree.*  `δ(G)` and `Δ(G)` denote the least and greatest
vertex degrees in `G`.

*Regular graph.*  `G` is `k`-**regular** when `d(v) = k` for every vertex `v`,
and **regular** when it is `k`-regular for some `k`.  Complete graphs, the
complete bipartite graphs `K_{n,n}`, and the `k`-cubes are all regular.

*Degree sequence* (exercise 1.5.5).  Listing the vertices as `v₁, …, v_ν`, the
sequence `(d(v₁), …, d(v_ν))`.  A sequence of non-negative integers is the degree
sequence of some graph exactly when its sum is even, and is called **graphic**
when it is the degree sequence of some *simple* graph.

*Edge graph* (exercise 1.5.10).  The graph whose vertex set is `E(G)`, two of its
vertices being joined exactly when the corresponding edges are adjacent in `G`
(that is, share an end).  This is Mathlib's `SimpleGraph.lineGraph`. -/

-- Thm 1.1 (handshaking / degree-sum): `∑ d(v) = 2ε`.
-- Mathlib: SimpleGraph.sum_degrees_eq_twice_card_edges
/-- **Theorem 1.1** (the handshaking / degree-sum theorem).
*`∑_{v ∈ V} d(v) = 2ε`.*

**Book proof** (B&M §1.5, verbatim).  *Consider the incidence matrix `M`.  The sum of
the entries in the row corresponding to vertex `v` is precisely `d(v)`, and therefore
`∑_{v ∈ V} d(v)` is just the sum of all entries in `M`.  But this sum is also `2ε`,
since (exercise 1.3.1a) each of the `ε` column sums of `M` is 2.*

**Proof.**  `G.sum_degrees_eq_twice_card_edges`, Mathlib.  ⚠ Mathlib's proof is a
direct double count over darts, *not* the book's route through the incidence matrix —
but Mathlib's `sum_incMatrix_apply_of_mem_edgeSet` is exactly B&M's exercise 1.3.1(a),
so the book's proof could be reconstructed from it if the incidence-matrix route were
wanted.  (Exercise 1.3.1(a) had a local restatement here; it was removed as a Mathlib
duplicate — see `ExtractionArchive/MathlibDuplicates.md`.)

**Reading.**  Adding up the degrees counts each edge twice, once from each end.  The
name comes from the reading: if each edge is a handshake, the total hands shaken is
twice the number of handshakes.  Loops are consistent, contributing `2` to their
single end. -/
theorem sum_degrees_eq_two_mul_edgeCard :
    ∑ v, G.degree v = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

-- Cor 1.1: the number of odd-degree vertices is even.
-- Mathlib: SimpleGraph.even_card_odd_degree_vertices
/-- **Corollary 1.1.**  *In any graph, the number of vertices of odd degree is
even.*

**Book proof** (B&M §1.5, verbatim).  *Let `V₁` and `V₂` be the sets of vertices of
odd and even degree in `G`, respectively.  Then*

    ∑_{v ∈ V₁} d(v) + ∑_{v ∈ V₂} d(v) = ∑_{v ∈ V} d(v)

*is even, by theorem 1.1.  Since `∑_{v ∈ V₂} d(v)` is also even, it follows that
`∑_{v ∈ V₁} d(v)` is even.  Thus `|V₁|` is even.*

**Proof.**  `G.even_card_odd_degree_vertices`, Mathlib.

**Reading.**  A sum of odd numbers is even precisely when there is an even number of
terms.  This tiny corollary is what §1.9 uses to derive Sperner's lemma, and through
it Brouwer's fixed-point theorem — the chapter's most striking application. -/
theorem even_card_odd_degree :
    Even (Finset.univ.filter (fun v => Odd (G.degree v))).card :=
  G.even_card_odd_degree_vertices

-- Ex 1.5.1: `δ ≤ 2ε/ν ≤ Δ`, stated multiplicatively as `ν·δ ≤ 2ε ≤ ν·Δ`.
/-- **Exercise 1.5.1.**  *`δ ≤ 2ε/ν ≤ Δ`.*

**Book proof.**  None — an exercise.

**Proof.**  Two `calc` chains, each three steps: rewrite `ν * δ` as the constant sum
`∑ _v, δ`, bound it termwise by `∑ v, degree v` via `Finset.sum_le_sum` and
`minDegree_le_degree`, then close with `sum_degrees_eq_twice_card_edges` (theorem
1.1).  The `Δ` half is the mirror image with `degree_le_maxDegree`.

**Reading.**  `2ε/ν` is the *average* degree, since the degrees sum to `2ε` and there
are `ν` of them; an average lies between the extremes.

**Formalisation.**  Stated multiplicatively to avoid division: `ν·δ ≤ 2ε ≤ ν·Δ`.
`[Nonempty V]` keeps `minDegree`/`maxDegree` meaningful — both are `sInf`/`sSup`-like
and degenerate on an empty carrier. -/
theorem degree_bounds [Nonempty V] :
    Fintype.card V * G.minDegree ≤ 2 * G.edgeFinset.card ∧
      2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
  constructor
  · -- every one of the `ν` degrees is at least `δ`, and they sum to `2ε`
    calc Fintype.card V * G.minDegree
        = ∑ _v : V, G.minDegree := by simp [Finset.card_univ, mul_comm]
      _ ≤ ∑ v, G.degree v := Finset.sum_le_sum fun v _ => G.minDegree_le_degree v
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  · -- and each is at most `Δ`
    calc 2 * G.edgeFinset.card
        = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _v : V, G.maxDegree := Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
      _ = Fintype.card V * G.maxDegree := by simp [Finset.card_univ, mul_comm]

-- Ex 1.5.3: a `k`-regular (`k > 0`) bipartite graph with bipartition `(s, t)` has `|s| = |t|`.
/-- **Exercise 1.5.3.**  *If a `k`-regular bipartite graph with `k > 0` has
bipartition `(X, Y)`, then `|X| = |Y|`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `s.ncard = t.ncard`).
1. **Count edges from the `X` side.**  Every edge has exactly one end in `s`
   (`hbip`), so `ε = ∑_{v ∈ s} degree v`.  Prove this as a `Finset.sum` over the
   edge finset partitioned by its `s`-end.
2. **Regularity** turns that into `ε = k * s.ncard`.
3. **Repeat from the `t` side**: `ε = k * t.ncard`.
4. `Nat.eq_of_mul_eq_mul_left hk` cancels `k`.

**Reading.**  Count the edges twice, once from each side.  ⚠ `hk : 0 < k` is
essential — a `0`-regular graph has no edges and its two parts can have any sizes.

**Formalisation.**  `IsBipartiteWith s t` is Mathlib's explicit-bipartition form,
stronger than `Colorable 2` and what step 1 needs.  `Set.ncard` rather than
`Finset.card`, so no decidability on `s`, `t` is required. -/
theorem regular_bipartite_card_eq {s t : Set V} (k : ℕ) (hk : 0 < k)
    (hreg : G.IsRegularOfDegree k) (hbip : G.IsBipartiteWith s t) :
    s.ncard = t.ncard := by
  sorry

-- Ex 1.5.8: every loopless graph has a bipartite spanning subgraph `H`
-- with `d_H(v) ≥ ½ d_G(v)` for all `v` (stated `d_G(v) ≤ 2·d_H(v)`).
/-- **Exercise 1.5.8** (starred).  *Every loopless graph `G` contains a bipartite
spanning subgraph `H` such that `d_H(v) ≥ ½ d_G(v)` for all `v ∈ V`.*

**Book proof.**  None — an exercise, and one the book **stars**.

**Skeleton** (for `∃ H ≤ G, H.Colorable 2 ∧ ∀ v, degree v ≤ 2 * (H.neighborSet v).ncard`).
1. **Search over bipartitions.**  For `X : Finset V`, let `cross X` be the number of
   edges with exactly one end in `X`.  Finitely many `X`, so pick one **maximising**
   `cross`.
2. `H :=` the spanning subgraph keeping exactly the crossing edges.  It is `≤ G` and
   `Colorable 2` (colour by membership in `X`).
3. **The local bound.**  Fix `v`; write `c` for its crossing degree and `i` for its
   degree inside its own part, so `degree v = c + i`.  Moving `v` to the other side
   changes `cross` by `i - c`.  Maximality gives `i - c ≤ 0`, i.e. `i ≤ c`, so
   `degree v = c + i ≤ 2c`.
4. Step 3 is exactly the goal, `c` being `(H.neighborSet v).ncard`.

**Reading.**  Split the vertices in two and keep only the crossing edges — automatically
bipartite and spanning — choosing the split to maximise crossings.  Then no vertex can
have more than half its edges inside its own part, or moving it would improve the
split.

**Formalisation.**  Conclusion in the cleared form `d_G(v) ≤ 2 d_H(v)` to stay in ℕ.
⚠ Step 3's `i - c ≤ 0` must be argued in `ℤ` or by `Nat.le_of_add_le_add`, not by
ℕ-subtraction. -/
theorem exists_bipartite_spanning_subgraph :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.Colorable 2 ∧
      ∀ v, G.degree v ≤ 2 * (H.neighborSet v).ncard := by
  sorry

/-- **Exercise 1.5.10(a), edge count.**  *If `G` is simple, the edge graph of `G`
has `∑_{v ∈ V(G)} C(d_G(v), 2)` edges.*

**Book proof.**  None — an exercise.

**Skeleton** (for `G.lineGraph.edgeFinset.card = ∑ v, (degree v).choose 2`).
1. **Charge each line-graph edge to a vertex.**  Two distinct edges of a *simple* `G`
   share **at most one** end, so a pair of adjacent edges determines a unique meeting
   vertex `v`.  This gives a map from `lineGraph.edgeFinset` to `V`.
2. **The fibre over `v` has `C(d(v), 2)` elements** — the unordered pairs of the
   `d(v)` edges at `v`, all of which are line-graph-adjacent.
3. `Finset.card_eq_sum_card_fiberwise` on steps 1–2.

**Reading.**  Two edges are adjacent in the edge graph exactly when they share an end;
simplicity makes that end unique, so the count localises at each vertex.

**Formalisation.**  ⚠ Step 1's uniqueness is where *simplicity* is spent — with
parallel edges two edges could share both ends and be counted twice.  Part (b) of the
exercise, not stated here, notes the edge graph of `K₅` is the complement of the
Petersen graph. -/
theorem lineGraph_edgeCard [DecidableRel G.lineGraph.Adj] :
    G.lineGraph.edgeFinset.card = ∑ v, (G.degree v).choose 2 := by
  sorry

-- DROPPED: Ex 1.5.5–1.5.7 (degree-sequence realizability, graphic sequences, Erdős–Gallai,
-- Havel–Hakimi) — these quantify over graphs with a *prescribed* degree sequence over an
-- unfixed vertex set / allow multigraphs; no clean `SimpleGraph V` signature here.

/-! ### Book statements for the dropped items, §1.5

*Exercise 1.5.5.*  A sequence `(d₁, …, d_n)` of non-negative integers is the
degree sequence of *some* graph if and only if `∑ dᵢ` is even.  (Loops and
parallel edges are allowed here, which is why this needs a multigraph carrier.)

*Exercise 1.5.6.*  A sequence is **graphic** when some *simple* graph has it as
degree sequence.  If `d` is graphic and `d₁ ≥ d₂ ≥ … ≥ d_n`, then `∑ dᵢ` is even
and `∑_{i≤k} dᵢ ≤ k(k-1) + ∑_{i>k} min{k, dᵢ}` for `1 ≤ k ≤ n`.  Erdős and
Gallai (1960) proved this necessary condition is also sufficient.

*Exercise 1.5.7* (Havel–Hakimi).  For a non-increasing `d`, let `d'` be
`(d₂-1, …, d_{d₁+1}-1, d_{d₁+2}, …, d_n)`.  Then `d` is graphic if and only if
`d'` is graphic, which yields a recursive construction algorithm. -/

/-! ## §1.6 Paths and connection

Mathlib: `G.Walk u v`, `p.IsPath`, `p.IsTrail`, `G.Reachable u v`,
`G.Connected`, `G.Preconnected`, `G.ConnectedComponent` (with `ω(G) =
Fintype.card G.ConnectedComponent`), and the distance `G.dist u v`. -/

/-! ### Book definitions, §1.6 (Paths and connection)

*Walk.*  A finite non-null sequence `W = v₀e₁v₁e₂v₂ … e_kv_k` whose terms are
alternately vertices and edges, such that for each `i` the ends of `eᵢ` are
`v_{i-1}` and `vᵢ`.  `W` is a walk **from** `v₀` **to** `v_k`, or a
`(v₀, v_k)`-walk; `v₀` is its **origin**, `v_k` its **terminus**, the remaining
`v₁, …, v_{k-1}` its **internal vertices**, and `k` its **length**.  Reversing
`W` gives `W⁻¹`; concatenating compatible walks at a shared endpoint gives
`WW'`; a **section** of `W` is a subsequence of consecutive terms.  In a simple
graph a walk is determined by its vertex sequence alone.

*Trail.*  A walk whose edges `e₁, …, e_k` are all distinct.  Its length is then
just its number of edges.

*Path.*  A trail whose vertices `v₀, …, v_k` are, in addition, all distinct.  The
word "path" is also used for the subgraph formed by those vertices and edges.

*Connected vertices, components, `ω(G)`.*  Two vertices `u`, `v` are
**connected** when a `(u, v)`-path exists.  Connection is an equivalence
relation on `V`, so `V` partitions into classes `V₁, …, V_ω`; the induced
subgraphs `G[V₁], …, G[V_ω]` are the **components** of `G`.  `G` is
**connected** when it has exactly one component, and **disconnected**
otherwise.  `ω(G)` denotes the number of components.

*Distance and diameter* (exercises 1.6.11–1.6.12).  For connected `u, v` the
**distance** `d_G(u, v)` is the length of a shortest `(u, v)`-path, and is
infinite if no such path exists.  The **diameter** of `G` is the maximum distance
between two of its vertices. -/

-- Ex 1.6.3: a simple graph with `δ ≥ k` has a path of length `k`.
/-- **Exercise 1.6.3.**  *If `G` is simple and `δ ≥ k`, then `G` has a path of
length `k`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `∃ u v p, p.IsPath ∧ p.length = k`).
1. **Take a longest path.**  Paths have `Nodup` support so their lengths are bounded
   by `ν`; the family is nonempty (`nil`), so a maximum is attained.  Call it `P`
   with terminus `v_m`.
2. **All neighbours of `v_m` lie on `P`** — otherwise `P.concat` extends it,
   contradicting maximality.
3. **Count.**  Those neighbours are `≥ δ ≥ k` distinct vertices, all on `P` and all
   `≠ v_m`, so `P` has `≥ k` vertices besides its terminus: `P.length ≥ k`.
4. **Truncate.**  Take the initial segment of `P` of length exactly `k` — `Walk.take`
   — which is still a path (a sub-walk of a path is a path).

**Reading.**  A longest path cannot be extended, so its endpoint's neighbours are all
already on it, forcing it to be long.  ⚠ Simplicity is what makes the `δ` neighbours
`δ` *distinct* vertices — and `SimpleGraph` supplies it for free. -/
theorem exists_path_length_of_minDegree (k : ℕ) (h : k ≤ G.minDegree) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = k := by
  sorry

-- Ex 1.6.4: `G` is connected iff every partition of `V` into two nonempty sets has a crossing edge.
/-- **Exercise 1.6.4.**  *`G` is connected if and only if, for every partition of
`V` into two nonempty sets `V₁` and `V₂`, there is an edge with one end in `V₁`
and one end in `V₂`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `G.Connected ↔ ∀ s, s.Nonempty → sᶜ.Nonempty → ∃ crossing edge`).
1. **(⇒).**  Given nonempty `s`, `sᶜ`, pick `u ∈ s`, `w ∈ sᶜ`.  Connectivity gives a
   walk `u ⇝ w`; along it there is a **first** vertex outside `s`
   (`Walk.takeUntil` or induction), and the edge into it crosses.
2. **(⇐).**  Contrapositive: if `G` is disconnected, take `s :=` the support of one
   connected component.  It is nonempty, its complement is nonempty (another
   component exists), and no edge crosses — both ends of an edge lie in the same
   component.
3. `Nonempty V` supplies `Connected`'s nonemptiness field in the `⇐` direction.

**Reading.**  Connectivity is exactly the statement that `V` admits no non-trivial cut
with no edges across it.

**Formalisation.**  The partition is a set `s` with its complement, both required
nonempty — equivalent to B&M's `(V₁, V₂)`. -/
theorem connected_iff_forall_partition_edge [Nonempty V] :
    G.Connected ↔
      ∀ s : Set V, s.Nonempty → sᶜ.Nonempty → ∃ u v, u ∈ s ∧ v ∈ sᶜ ∧ G.Adj u v := by
  sorry

-- Ex 1.6.5(a): a simple graph with `ε > C(ν-1, 2)` is connected.
/-- **Exercise 1.6.5(a).**  *If `G` is simple and `ε > C(ν-1, 2)`, then `G` is
connected.*

**Book proof.**  None — an exercise.

**Skeleton** (for `C(ν-1,2) < ε → G.Connected`).  Contrapositive.
1. Assume `G` disconnected.  Exercise 1.6.4 gives a partition `(s, sᶜ)` into nonempty
   parts with no crossing edge, say of sizes `p` and `ν - p`, `1 ≤ p ≤ ν - 1`.
2. **Every edge lies inside one part**, so `ε ≤ C(p,2) + C(ν-p,2)` by exercise 1.1.3
   applied to each induced subgraph.
3. **The bound is maximised at `p = 1`.**  `C(p,2) + C(ν-p,2) ≤ C(ν-1,2)` for
   `1 ≤ p ≤ ν-1` — expand both sides and `nlinarith`, or induct on `p`.  ⚠ This is
   the only real computation; do it in ℤ or with the doubled form
   `2·C(n,2) = n(n-1)` to avoid ℕ-division.
4. So `ε ≤ C(ν-1,2)`, contradicting `h`.

**Reading.**  A disconnected simple graph is sparsest-constrained in the most lopsided
split.  The bound is **sharp**: part (b), not stated here, asks for a disconnected
simple graph with exactly `C(ν-1,2)` edges — `K_{ν-1}` plus one isolated vertex. -/
theorem connected_of_edgeCard_gt
    (h : (Fintype.card V - 1).choose 2 < G.edgeFinset.card) :
    G.Connected := by
  sorry

-- Ex 1.6.7: if `G` is disconnected then its complement is connected.
/-- **Exercise 1.6.7.**  *If `G` is disconnected, then `Gᶜ` is connected.*

**Book proof.**  None — an exercise.

**Skeleton** (for `¬ G.Connected → Gᶜ.Connected`).
1. Fix `u`, `v`; show `Gᶜ.Reachable u v`, then add `Nonempty V`.
2. **Case `u`, `v` in different `G`-components.**  Then `¬ G.Adj u v`, so `Gᶜ.Adj u v`
   (given `u ≠ v`) — a one-edge walk.
3. **Case same component.**  Disconnectedness gives a vertex `w` in another
   component.  Then `¬ G.Adj u w` and `¬ G.Adj v w`, so `u — w — v` is a walk in
   `Gᶜ`.
4. **`u = v`** is `Reachable.refl`.

**Reading.**  Every pair is joined in `Gᶜ` by a path of length at most `2`, so `Gᶜ` is
connected — indeed of diameter `≤ 2`.  Equivalently: **at least one of `G`, `Gᶜ` is
always connected**.

**Formalisation.**  ⚠ Steps 2–3 need `u ≠ w` and `v ≠ w`, which follow from them being
in different components; and "different components" must be extracted from
`¬ Connected` — `Preconnected` failing gives an unreachable pair. -/
theorem compl_connected_of_not_connected [Nonempty V] (h : ¬ G.Connected) :
    Gᶜ.Connected := by
  sorry

-- Ex 1.6.8(a), general form: adding edges can only merge components, never split them.
-- Extracted because `Trees.lean` (corollary 2.7) needs exactly this and says so.
/-- **Component count is antitone in the subgraph order.**  If `H ≤ K` then
`ω(K) ≤ ω(H)` — adding edges can only merge components.

**Provenance.**  Not a book statement.  This is the general lemma that exercise
1.6.8(a) below is the single-edge instance of, and it is extracted here because
`Trees.lean`'s skeleton for corollary 2.7 asks for it by name: *"the monotonicity
`H ≤ K → ω(K) ≤ ω(H)` is used here and is worth a standalone lemma — chapter 1's
exercise 1.6.8(a) needs the same fact."*  Both call sites are served by this one
declaration.

**Skeleton.**
1. **The induced map on components.**  `h : H ≤ K` means every `H`-edge is a `K`-edge,
   so `H.Reachable u v → K.Reachable u v`; this descends to a map
   `f : H.ConnectedComponent → K.ConnectedComponent` via
   `ConnectedComponent.lift (K.connectedComponentMk ·)`.
2. **`f` is surjective.**  Every `K`-component is `K.connectedComponentMk v` for some
   `v` (components are quotient classes of a nonempty type of representatives), and
   `f (H.connectedComponentMk v)` is that class.
3. `Nat.card_le_card_of_surjective f` (or `Finite.card_le_of_surjective`) gives the
   bound.  `Finite V` supplies finiteness of both quotients.

**Formalisation.**  Stated with `Nat.card`, matching `Trees.numComponents`, so that no
`DecidableEq` on the quotient is needed.  ⚠ Exercise 1.6.8(a) below uses
`Fintype.card`; over a `Fintype` carrier the two agree by `Nat.card_eq_fintype_card`,
but the transfer must be written explicitly at the call site. -/
theorem card_connectedComponent_le_of_le {H K : SimpleGraph V} (h : H ≤ K) :
    Nat.card K.ConnectedComponent ≤ Nat.card H.ConnectedComponent := by
  sorry

-- Ex 1.6.8(a): deleting one edge changes the number of components by at most one:
-- `ω(G) ≤ ω(G - e) ≤ ω(G) + 1`.
/-- **Exercise 1.6.8(a).**  *If `e ∈ E`, then `ω(G) ≤ ω(G - e) ≤ ω(G) + 1`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `ω(G) ≤ ω(G-e) ≤ ω(G) + 1`).
1. **Lower bound.**  `G.deleteEdges {e} ≤ G`, so this is exactly
   `card_connectedComponent_le_of_le` directly above, transferred from `Nat.card` to
   `Fintype.card` by `Nat.card_eq_fintype_card`.
2. **Upper bound.**  Write `e = s(x,y)`.  The same map is **injective off the class of
   `x`**: two vertices separated by deleting `e` were connected in `G` only via a walk
   through `e`, hence one is reachable from `x` and the other from `y`.  So at most
   one `G`-component splits, and into at most two pieces.
3. Conclude `ω(G-e) ≤ ω(G) + 1` by a fibre count on the map of step 1: every fibre is
   a singleton except possibly one, of size `≤ 2`.

**Reading.**  Deleting an edge only destroys connections, never creates them; and it
affects only the component containing `e`, which can break into at most the parts
reachable from each end.  An edge whose deletion *does* raise the count is a **cut
edge**, the subject of §2.3.  ⚠ Part (b), not stated here, notes the analogue fails for
*vertex* deletion — removing one vertex can create many components. -/
theorem components_deleteEdge {e : Sym2 V} (he : e ∈ G.edgeSet) :
    Fintype.card G.ConnectedComponent
        ≤ Fintype.card (G.deleteEdges {e}).ConnectedComponent ∧
      Fintype.card (G.deleteEdges {e}).ConnectedComponent
        ≤ Fintype.card G.ConnectedComponent + 1 := by
  sorry

-- Ex 1.6.12: if `G` has diameter > 3 then `Gᶜ` has diameter < 3.
/-- **Exercise 1.6.12.**  *If `G` has diameter greater than three, then `Gᶜ` has
diameter less than three.*

**Book proof.**  None — an exercise.

**Skeleton** (for `3 < G.diam → Gᶜ.diam < 3`).
1. `3 < diam` gives `u`, `v` with `d_G(u,v) > 3`.
2. **Key consequences.**  No common neighbour of `u`, `v` (else `d = 2`), and no edge
   of `G` joins `N(u)` to `N(v)` (else `d = 3`).  So in `Gᶜ`, every vertex of `N(u)`
   is adjacent to every vertex of `N(v)`, and `u`, `v` are `Gᶜ`-adjacent to
   everything outside their own neighbourhoods.
3. **Every pair is within `2` in `Gᶜ`.**  Case on where the two vertices sit relative
   to `N(u)`, `N(v)`, `{u,v}` and the rest; in each case exhibit a common
   `Gᶜ`-neighbour (usually `u` or `v`).
4. Hence `Gᶜ.diam ≤ 2 < 3`.

**Reading.**  A graph and its complement cannot both be "spread out": if `G` is very
stretched, `Gᶜ` must be very compact.

**Formalisation.**  ⚠ `G.diam` is `ℕ`-valued and Mathlib returns `0` for a
disconnected graph, so `3 < G.diam` silently carries "`G` is connected" — worth
making explicit before relying on step 1. -/
theorem compl_diam_lt_of_diam_gt (h : 3 < G.diam) : Gᶜ.diam < 3 := by
  sorry

-- Ex 1.6.14: a simple connected non-complete graph has vertices `u, v, w`
-- with `uv, vw ∈ E` but `uw ∉ E`.
/-- **Exercise 1.6.14.**  *If `G` is simple and connected but not complete, then
`G` has three vertices `u`, `v` and `w` such that `uv, vw ∈ E` and `uw ∉ E`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `∃ u v w, G.Adj u v ∧ G.Adj v w ∧ ¬ G.Adj u w`).
1. `hne : G ≠ ⊤` gives a non-adjacent pair `x ≠ y`.
2. `hc` gives a walk `x ⇝ y`; take a **shortest** one, `P`.
3. `P.length ≥ 2`, since length `0` means `x = y` and length `1` means `G.Adj x y`.
4. **Read off three consecutive vertices** `u, v, w` at the start of `P`, so
   `G.Adj u v` and `G.Adj v w`.
5. `¬ G.Adj u w`: otherwise the shortcut `u — w` gives a strictly shorter `x ⇝ y`
   walk, contradicting minimality of `P`.

**Reading.**  A connected non-complete graph always contains an induced path on three
vertices — adjacency is transitive only when the graph is a disjoint union of complete
graphs.  ★ Consumed by Brooks' theorem 8.4, whose 3-connected case opens by invoking
exactly this. -/
theorem exists_induced_path_of_connected_not_complete
    (hc : G.Connected) (hne : G ≠ ⊤) :
    ∃ u v w, G.Adj u v ∧ G.Adj v w ∧ ¬ G.Adj u w := by
  sorry

/-! ## §1.7 Cycles

Mathlib: `p.IsCycle` (closed trail with distinct internal vertices), `G.girth`
(length of a shortest cycle). -/

/-! ### Book definitions, §1.7 (Cycles)

*Closed walk.*  A walk of positive length whose origin and terminus coincide.

*Cycle.*  A closed trail whose origin and internal vertices are distinct.  As
with paths, "cycle" is also used for the corresponding subgraph.  A cycle of
length `k` is a `k`-**cycle**, and is **odd** or **even** according to the parity
of `k`; a `3`-cycle is a **triangle**.

*Girth* (exercise 1.7.4).  The length of a shortest cycle in `G`; if `G` has no
cycles at all its girth is defined to be infinite. -/

-- Thm 1.2: a graph is bipartite iff it contains no odd cycle.
-- Mathlib: SimpleGraph.two_colorable_iff_forall_loop_even (equivalent loop form).
/-- **Theorem 1.2.**  *A graph is bipartite if and only if it contains no odd
cycle.*

**Book proof** (B&M §1.7, verbatim).  *Suppose that `G` is bipartite with bipartition
`(X, Y)`, and let `C = v₀ v₁ … v_k v₀` be a cycle of `G`.  Without loss of generality
we may assume that `v₀ ∈ X`.  Then, since `v₀v₁ ∈ E` and `G` is bipartite, `v₁ ∈ Y`.
Similarly `v₂ ∈ X` and, in general, `v_{2i} ∈ X` and `v_{2i+1} ∈ Y`.  Since
`v₀ ∈ X`, `v_k ∈ Y`.  Thus `k = 2i + 1`, for some `i`, and it follows that `C` is
even.*

*[Conversely] … `X = {x ∈ V | d(u, x) is even}`, `Y = {y ∈ V | d(u, y) is odd}`.  We
shall show that `(X, Y)` is a bipartition of `G`.  Suppose that `v` and `w` are two
vertices of `X`.  Let `P` be a shortest `(u, v)`-path and `Q` be a shortest
`(u, w)`-path.  Denote by `u₁` the last vertex common to `P` and `Q`.  Since `P` and
`Q` are shortest paths, the `(u, u₁)`-sections of both `P` and `Q` are shortest
`(u, u₁)`-paths and, therefore, have the same length.  Now, since the lengths of both
`P` and `Q` are even, the lengths of the `(u₁, v)`-section `P₁` of `P` and the
`(u₁, w)`-section `Q₁` of `Q` must have the same parity.  It follows that the
`(v, w)`-path `P₁⁻¹Q₁` is of even length.  If `v` were joined to `w`, `P₁⁻¹Q₁wv`
would be a cycle of odd length, contrary to the hypothesis.  Therefore no two vertices
in `X` are adjacent; similarly, no two vertices in `Y` are adjacent.*

**Skeleton** (for `G.Colorable 2 ↔ ∀ u c, c.IsCycle → Even c.length`).
1. **(⇒).**  A `2`-colouring `f` alternates along any walk, so `f` at position `i` is
   determined by `i`'s parity; closing the cycle forces the length even.  Formally,
   induct along `c` proving `f (c.getVert i) = f u ↔ Even i`.
2. **(⇐).**  Reduce to connected `G` — colour each component independently, so it
   suffices to `2`-colour each.
3. Fix `u`; colour `x` by `d(u,x) % 2`.
4. **Properness.**  For `G.Adj v w`, `|d(u,v) - d(u,w)| ≤ 1` (triangle inequality) and
   they cannot be equal: the book's `P₁⁻¹Q₁ + wv` would be an odd cycle.  So the
   parities differ.
5. ⚠ Step 4 is the fiddly part — extracting an actual *cycle* from the two shortest
   paths requires the "last common vertex" argument, and the result is a cycle only
   after `bypass`-style cleanup.

**Reading.**  Odd cycles are the sole obstruction to `2`-colourability — the fact that
makes chapter 8 turn on odd cycles throughout.

**Formalisation.**  Bipartiteness as `G.Colorable 2`; Mathlib's
`two_colorable_iff_forall_loop_even` is an equivalent *loop*-based form and may close
this more directly than the cycle form. -/
theorem bipartite_iff_no_odd_cycle :
    G.Colorable 2 ↔ ∀ (u : V) (c : G.Walk u u), c.IsCycle → Even c.length := by
  sorry

-- Ex 1.7.1: an edge lying in a closed trail lies in a cycle.
/-- **Exercise 1.7.1.**  *If an edge `e` is in a closed trail of `G`, then `e` is
in a cycle of `G`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `∃ v d, d.IsCycle ∧ e ∈ d.edges`).
1. Among all closed **trails** containing `e`, choose one of shortest length —
   possible since lengths are bounded by `ε` and the family is nonempty (`c`).
2. **It has distinct internal vertices.**  If a vertex `w` recurred away from the
   endpoints, splitting at `w` gives two shorter closed trails whose edge sets
   partition the original; `e` lies in one of them, contradicting minimality.
3. Distinct internal vertices plus closed plus positive length is exactly `IsCycle`.

**Reading.**  A closed trail may revisit vertices, so it need not be a cycle; the
claim is that it can be pared down to one through any chosen edge.  ⚠ The analogous
statement for *walks* is **false** — a walk may traverse the same edge back and forth
with no cycle present — which is why `ht : c.IsTrail` (distinct edges) is a hypothesis
and not decoration.

**Formalisation.**  `hpos : 0 < c.length` excludes the trivial closed walk, for which
`he` would be unsatisfiable anyway but which would otherwise complicate step 1. -/
theorem edge_in_cycle_of_closed_trail {u : V} (c : G.Walk u u)
    (ht : c.IsTrail) (hpos : 0 < c.length) {e : Sym2 V} (he : e ∈ c.edges) :
    ∃ (v : V) (d : G.Walk v v), d.IsCycle ∧ e ∈ d.edges := by
  sorry

-- Ex 1.7.2: `δ ≥ 2` implies `G` contains a cycle.
/-- **Exercise 1.7.2.**  *If `δ ≥ 2`, then `G` contains a cycle.*

**Book proof.**  None — an exercise.

**Skeleton** (for `∃ v c, c.IsCycle`).
1. Take a **longest path** `P = v₀v₁ … v_m` (as in exercise 1.6.3 step 1).
2. `δ ≥ 2` gives `v₀` a neighbour `x` besides `v₁`.
3. **`x` lies on `P`** — otherwise prepending it extends `P`, contradicting
   maximality.  So `x = vᵢ` with `i ≥ 2`.
4. `v₀v₁ … vᵢv₀` is closed, of positive length, with distinct internal vertices
   (a sub-path of `P`) — a cycle.

**Reading.**  If every vertex offers a second way out you can never get stuck, so
walking forward must eventually revisit a vertex, and the first revisit closes a
cycle.  ★ Contrapositively, **an acyclic graph always has a vertex of degree ≤ 1** —
used repeatedly in chapter 2's theory of trees, and by chapter 12's lemma 12.2.1. -/
theorem exists_cycle_of_minDegree_ge_two (h : 2 ≤ G.minDegree) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  sorry

-- Ex 1.7.3: a simple graph with `δ ≥ 2` contains a cycle of length ≥ `δ + 1`.
/-- **Exercise 1.7.3** (starred).  *If `G` is simple and `δ ≥ 2`, then `G`
contains a cycle of length at least `δ + 1`.*

**Book proof.**  None — an exercise, and one the book **stars**.

**Skeleton** (for `∃ v c, c.IsCycle ∧ δ + 1 ≤ c.length`).
1. Take a longest path `P = v₀v₁ … v_m`; as in exercise 1.6.3, **every** neighbour of
   `v₀` lies on `P`, and there are `≥ δ` of them, all distinct (simplicity).
2. Let `vᵢ` be the neighbour of `v₀` **furthest along** `P`.
3. **Count.**  All `≥ δ` neighbours of `v₀` sit among `v₁, …, vᵢ`, so `i ≥ δ`.
4. The cycle `v₀v₁ … vᵢv₀` has length `i + 1 ≥ δ + 1`.

**Reading.**  Sharpens exercise 1.7.2 from "some cycle exists" to a length bound: a
graph in which every vertex has many neighbours cannot consist only of short cycles.
★ This is chapter 10's exercise 10.1.7 one dimension down — the directed version bounds
directed cycles by `max{δ⁻,δ⁺} + 1` and is used inside Ghouila-Houri's theorem 10.4. -/
theorem exists_long_cycle_of_minDegree (h : 2 ≤ G.minDegree) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ G.minDegree + 1 ≤ c.length := by
  sorry

-- Ex 1.7.4(a): a `k`-regular graph of girth 4 has at least `2k` vertices.
/-- **Exercise 1.7.4(a).**  *A `k`-regular graph of girth four has at least `2k`
vertices.*

**Book proof.**  None — an exercise.

**Skeleton** (for `2 * k ≤ ν`).
1. **Girth `4` ⟹ triangle-free** — a triangle would be a cycle of length `3 < 4`.
2. Pick an edge `uv` (one exists: girth is finite, so `G` has a cycle).
3. **`N(u)` and `N(v)` are disjoint** — a common neighbour would close a triangle with
   `uv`.
4. Both have `k` elements by `hreg`, so `ν ≥ |N(u)| + |N(v)| = 2k`.

**Reading.**  ⚠ B&M add that, up to isomorphism, there is exactly **one** such graph on
`2k` vertices, namely `K_{k,k}`; only the counting half is stated here, and the
uniqueness half would be a substantially harder separate result. -/
theorem girth_four_regular_card_ge (k : ℕ)
    (hreg : G.IsRegularOfDegree k) (hg : G.girth = 4) :
    2 * k ≤ Fintype.card V := by
  sorry

-- Ex 1.7.4(b): a `k`-regular graph of girth 5 has at least `k² + 1` vertices.
/-- **Exercise 1.7.4(b).**  *A `k`-regular graph of girth five has at least
`k² + 1` vertices.*

**Book proof.**  None — an exercise.

**Skeleton** (for `k ^ 2 + 1 ≤ ν`).
1. **Girth `5` ⟹ no triangles and no quadrilaterals**, i.e. no two vertices have two
   common neighbours, and no two adjacent vertices have any.
2. Fix `v`.  Its `k` neighbours are distinct; each has `k - 1` further neighbours
   besides `v`.
3. **All these are distinct.**  Two neighbours of `v` sharing a further neighbour
   would close a `4`-cycle; a further neighbour equal to a neighbour of `v` would
   close a triangle; and none equals `v`.
4. Count: `1 + k + k(k-1) = k² + 1 ≤ ν`.

**Reading.**  Graphs attaining this bound with diameter two are the **Moore graphs**
of exercise 1.7.5; Hoffman and Singleton showed they exist only for `k = 2, 3, 7` and
possibly `57`.  The case `k = 3` is the **Petersen graph** — the same graph chapter 9
uses as its counterexample to Tait's approach.

**Formalisation.**  ⚠ `k - 1` is ℕ-subtraction; `k = 0` makes the statement `1 ≤ ν`
and `girth = 5` unsatisfiable, so the degenerate case is vacuous — but check it rather
than assume it. -/
theorem girth_five_regular_card_ge (k : ℕ)
    (hreg : G.IsRegularOfDegree k) (hg : G.girth = 5) :
    k ^ 2 + 1 ≤ Fintype.card V := by
  sorry

-- Ex 1.7.6(a): `ε ≥ ν` implies `G` contains a cycle.
/-- **Exercise 1.7.6(a).**  *If `ε ≥ ν`, then `G` contains a cycle.*

**Book proof.**  None — an exercise.

**Skeleton** (for `ν ≤ ε → ∃ v c, c.IsCycle`).  Contrapositive.
1. Assume `G` is acyclic, i.e. `G.IsAcyclic`.
2. **An acyclic graph is a forest, with `ε = ν - ω`** — B&M's theorem 2.2, from the
   *next* chapter.  ⚠ This is the out-of-chapter import; alternatively use Mathlib's
   `IsAcyclic` API directly, which relates acyclicity to unique paths and may give the
   edge count more cheaply.
3. So `ε = ν - ω ≤ ν - 1 < ν`, contradicting `h`.

**Reading.**  Each edge added to a forest either joins two different components —
possible at most `ν - 1` times — or joins two already-connected vertices, immediately
closing a cycle.  ⚠ Part (b), due to Pósa and not stated here, strengthens this:
`ε ≥ ν + 4` forces two **edge-disjoint** cycles.

**Formalisation.**  ✅ **Hypothesis repaired.**  Step 2 needs `ω ≥ 1`, i.e.
`Nonempty V`.  Without it the statement is **false** on an empty carrier, where
`ν = ε = 0` so `h` holds vacuously while no cycle exists (indeed no vertex `v` exists
to base one at).  `[Nonempty V]` has been added; it is not in B&M only because the
book's graphs are nonempty by convention. -/
theorem exists_cycle_of_edgeCard_ge [Nonempty V]
    (h : Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  sorry

/-! ## §1.8 The shortest path problem (application)

DROPPED: Dijkstra's algorithm is a *procedure*, not a theorem — there is no
statable proposition here beyond the recurrence `d(u₀, S̄) = min {d(u₀,u) + w(uv)}`,
which is an algorithmic invariant.  The underlying distance notion is Mathlib's
`G.dist` / weighted analogues; see §1.6 for the metric facts. -/

/-! ### Book content, §1.8 (The shortest path problem)

*Weighted graph.*  A graph together with a real number `w(e)`, the **weight**, on
each edge.  The weight `w(H)` of a subgraph `H` is the sum of the weights of its
edges.  In the shortest path problem the weights are non-negative distances, and
one seeks a minimum-weight path between two specified vertices `u₀` and `v₀`.
For weighted graphs the book renames the weight of a path its **length**, and
the minimum weight of a `(u, v)`-path the **distance** `d(u, v)`; with all
weights equal to one these agree with the unweighted notions of §1.6.

*The key recurrence.*  If `S ⊆ V` with `u₀ ∈ S` and `S̄ = V \ S`, then any
shortest path from `u₀` into `S̄` leaves `S` exactly once, so

    d(u₀, S̄) = min { d(u₀, u) + w(uv) : u ∈ S, v ∈ S̄ }.

*Dijkstra's algorithm.*  Starting from `S₀ = {u₀}`, build an increasing chain
`S₀ ⊆ S₁ ⊆ … ⊆ S_{ν-1}` so that at the end of stage `i` shortest paths from `u₀`
to every vertex of `Sᵢ` are known.  Each vertex `v` carries a label `l(v)`, an
upper bound on `d(u₀, v)`, initialised to `l(u₀) = 0` and `l(v) = ∞` otherwise.
At each stage every `v ∈ S̄ᵢ` has `l(v)` replaced by `min{l(v), l(uᵢ) + w(uᵢv)}`,
the vertex attaining the smallest label is added to `S`, and the process repeats
until all vertices are absorbed.  The shortest paths found at each stage together
form a tree, so the algorithm can be seen as growing a tree out of `u₀`.

*Good algorithms.*  Following Edmonds (1965), an algorithm is **good** when the
number of steps it needs is bounded by a polynomial in `ν` and `ε`.  Dijkstra's
algorithm uses about `5ν²/2` additions and comparisons, so it is of order `ν²`
and hence good. -/

/-! ## §1.9 Sperner's lemma (application)

DROPPED: Thm 1.3 (Sperner's lemma) concerns *simplicial subdivisions of a
triangle* together with a *proper 3-labelling*, and asserts an odd number of
"distinguished" (rainbow) triangles.  Formalising it faithfully needs a whole
combinatorial-geometry API (simplices, subdivisions, barycentric coordinates)
that has no clean `SimpleGraph`-level signature, so it is omitted here.  Bondy &
Murty derive it from Cor 1.1 (`even_card_odd_degree`), which *is* stated above. -/

/-! ### Book content, §1.9 (Sperner's lemma)

*Simplicial subdivision.*  Let `T` be a closed triangle in the plane.  A
subdivision of `T` into finitely many smaller triangles is **simplicial** when
any two of the small triangles that meet do so in either a single common vertex
or a whole common side.

*Proper labelling.*  A labelling of the vertices of the subdivision by the three
symbols `0`, `1`, `2` is **proper** when (i) the three corners of `T` receive the
three distinct labels `0`, `1`, `2` in some order, and (ii) for `i < j`, each
vertex lying on the side of `T` joining the corners labelled `i` and `j` is
labelled either `i` or `j`.  A small triangle receiving all three labels is
called **distinguished**.

*Theorem 1.3 (Sperner's lemma).*  Every properly labelled simplicial subdivision
of a triangle has an odd number of distinguished triangles.

*Proof sketch.*  Let `T₀` be the region outside `T` and `T₁, …, T_n` the small
triangles.  Form a graph on `{v₀, v₁, …, v_n}`, joining `vᵢ` to `vⱼ` whenever the
common boundary of `Tᵢ` and `Tⱼ` is a side whose two endpoints are labelled `0`
and `1`.  The outer vertex `v₀` has odd degree, so by corollary 1.1 (formalised
above as `even_card_odd_degree`) an odd number of the remaining `vᵢ` also have
odd degree.  No `vᵢ` can have degree three, so those of odd degree have degree
one — and `vᵢ` has degree one exactly when `Tᵢ` is distinguished.

*Consequence.*  Sperner's lemma yields Brouwer's fixed-point theorem: writing
points of `T` in barycentric coordinates `(a₀, a₁, a₂)` and setting
`Sᵢ = {x : aᵢ' ≤ aᵢ}` for a continuous `f`, a proper labelling with each vertex
labelled `i` lying in `Sᵢ` exists, so arbitrarily fine subdivisions produce
distinguished triangles whose vertices lie in `S₀`, `S₁`, `S₂` respectively.
Since the `Sᵢ` are closed, `S₀ ∩ S₁ ∩ S₂ ≠ ∅`, and any point of that
intersection is a fixed point of `f`. -/

end SimpleGraph
