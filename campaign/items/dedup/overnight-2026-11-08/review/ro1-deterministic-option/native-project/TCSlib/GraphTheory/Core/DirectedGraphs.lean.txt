import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Combinatorics.Quiver.ConnectedComponent
import Mathlib.Logic.Relation
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.List.Chain
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Bondy & Murty, *Graph Theory with Applications* — Chapter 10: Directed Graphs

Sorry-skeleton extracted from `papers/bondy-murty-ch10-directed-graphs.md`.

The carrier is Mathlib's `Digraph V` (a bare `Adj : V → V → Prop` structure with a lattice API but
**no** walk/path/degree/connectivity development).  Directed walks are borrowed from `Quiver.Path`
through the one-line bridge `Digraph.toQuiver`; reachability is `Relation.ReflTransGen`.  Almost every
directed notion is a custom `def` here because Mathlib has none.

Every proof body is `sorry`; this is a scaffold for sorry-driven development (fill one stub at a time,
`lake build` after each).  The outline's `import TCSlib.GraphTheory.Connectivity.Defs` refers to a repo
file this scaffold does not import, so `edgeConnectivity`/`IsEdgeCut` are restated locally below.
-/

/-! ## Local re-statement of edge-connectivity (repo `Connectivity` file not imported) -/

/-- An **edge cut** of `G`: a set of edges whose deletion disconnects `G`.

**Book definition** (B&M §3.1, verbatim).  *Recall that an edge cut of `G` is a
subset of `E` of the form `[S, S̄]`, where `S` is a nonempty proper subset of `V`.
A `k`-edge cut is an edge cut of `k` elements.  If `G` is nontrivial and `E'` is an
edge cut of `G`, then `G - E'` is disconnected.*

**Reading.**  Needed here by exercise 10.3.6(b) and theorems 10.5–10.6, which
relate the edge-connectivity of a graph to the arc-connectivity of its
orientations — the whole point of §10.6 being that `2`-edge-connectivity is exactly
what a diconnected orientation requires.

**Formalisation.**  The book defines an edge cut *by its shape* `[S, S̄]` and then
observes that deleting one disconnects; this takes the observation as the
condition, which is the repo's notion and the one theorems 10.5–10.6 consume.  The
minimum size is the same either way, since every disconnecting edge set contains a
`[S, S̄]` for `S` a component of the remainder. -/
def SimpleGraph.IsEdgeCut {V : Type*} (G : SimpleGraph V) (F : Finset (Sym2 V)) : Prop :=
  (↑F : Set (Sym2 V)) ⊆ G.edgeSet ∧ ¬ (G.deleteEdges (↑F : Set (Sym2 V))).Connected

open scoped Classical in
/-- Edge connectivity `κ'(G)`.

**Book definition** (B&M §3.1, verbatim).  *We … define the edge connectivity
`κ'(G)` of `G` to be the minimum `k` for which `G` has a `k`-edge cut.  If `G` is
trivial, `κ'(G)` is defined to be zero.  …  `G` is said to be `k`-edge-connected if
`κ'(G) ≥ k`.*

**Reading.**  The least number of edges one must cut to break `G` apart.  "`G` is
`k`-edge-connected" is spelled `k ≤ edgeConnectivity G` throughout this file — see
`robbins_orientation` (`k = 2`) and `exists_kArcConnected_orientation_of_eulerian`.

**Formalisation.**  Mathlib has no edge-connectivity, so this is the repo's notion
restated locally.  `sInf ∅ = 0` in `ℕ` reproduces the book's trivial-graph
convention automatically — but it also means a graph with *no* edge cut (a
one-vertex graph) gets `κ' = 0`, which is the source of the `[Nontrivial V]` gap in
`associatedDigraph_isKArcConnected_iff` below. -/
noncomputable def edgeConnectivity {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ F : Finset (Sym2 V), G.IsEdgeCut F ∧ F.card = n}

namespace Digraph

/-! ## The shared directed-graph layer

Every def below is real and compiling except `arcsOf`, whose structural recursion the outline leaves
unspecified (stubbed `:= sorry`).  `toQuiver` is deliberately **not** an `instance`: ch10 juggles
several digraphs on one vertex type at once. -/

/-! ### Bridge to `Quiver` -/

/-- The bridge `Digraph → Quiver`: `Quiver.{0} V` has `Hom : V → V → Prop`, exactly `Digraph.Adj`.

**Book context.**  B&M have no such notion — it is pure plumbing.  It exists so
that §10.1's *directed walk* can be borrowed rather than rebuilt: *A directed walk
in `D` is a finite non-null sequence `W = (v₀, a₁, v₁, …, a_k, v_k)`, whose terms
are alternately vertices and arcs, such that, for `i = 1, 2, …, k`, the arc `aᵢ`
has head `vᵢ` and tail `v_{i-1}`.*

**Reading.**  A quiver is a vertex set together with, for each ordered pair, a
*type* of arrows.  Taking that type to be a `Prop` — arrow or no arrow — recovers
exactly a digraph, and Mathlib's `Quiver.Path` then supplies directed walks for
free, which `Digraph` (a bare `Adj` with a lattice API) does not.

**Formalisation.**  ⚠ Deliberately **not** an `instance`.  The chapter routinely
handles several digraphs on one vertex type at once — `D` and its converse `D̆`,
`D` and a reorientation of one arc (exercise 10.2.1) — and a global instance would
make `Quiver.Path` ambiguous between them.  The cost is that every use site must
write `@Quiver.Path V D.toQuiver u v` explicitly, which is why the statements below
are visually heavy. -/
def toQuiver {V : Type*} (D : Digraph V) : Quiver.{0} V := ⟨D.Adj⟩

/-! ### Directed walks / paths / cycles.  ⚠ `Quiver.Path` IS the directed WALK. -/

/-- A directed **path**: a `Quiver.Path` with no repeated vertex.

**Book definition** (B&M §10.1, verbatim).  *A directed walk in `D` is a finite
non-null sequence `W = (v₀, a₁, v₁, …, a_k, v_k)`, whose terms are alternately
vertices and arcs, such that, for `i = 1, 2, …, k`, the arc `aᵢ` has head `vᵢ` and
tail `v_{i-1}`.  …  A directed trail is a directed walk that is a trail; directed
paths, directed cycles and directed tours are similarly defined.*

**Reading.**  Follow the arrows, never against them; a directed path additionally
never revisits a vertex.  The book stresses (figure 10.3) that there is *no close
relationship between the lengths of paths and directed paths in a digraph* — the
digraph there has arbitrarily long paths but no directed path of length above one.
Theorem 10.1 is remarkable precisely because it recovers control of directed-path
length from the chromatic number.

**Formalisation.**  ⚠ `Quiver.Path` **is** the directed walk, so a directed path is
a `Quiver.Path` with `Nodup` vertices.  Note the book's directed walks are
*non-null*, whereas `Quiver.Path.nil` is available here; that mismatch is harmless
for paths but bites for Euler tours (see `IsDirectedEulerTour`). -/
def IsDirectedPath {V : Type*} (D : Digraph V) {u v : V} (p : @Quiver.Path V D.toQuiver u v) : Prop :=
  (@Quiver.Path.vertices V D.toQuiver u v p).Nodup

/-- A directed **cycle**: a positive-length closed walk whose vertices (bar the repeated endpoint)
are distinct.

**Book definition** (B&M §10.1).  The book defines it only by analogy — *directed
paths, directed cycles and directed tours are similarly defined* — so the unfolding
here (a closed directed walk of positive length whose vertices, apart from the
coinciding endpoints, are distinct) follows §1.4's cycle.

**Reading.**  Follow the arrows all the way round and return to where you started,
never repeating a vertex en route.  Directed cycles are the subject of §10.3: Moon
(theorem 10.3) finds them of every length in a diconnected tournament, and
Ghouila-Houri (theorem 10.4) finds a spanning one under a degree condition.

**Formalisation.**  `0 < length` excludes `nil`; `vertices.tail.Nodup` allows the
repeated basepoint at the two ends while forbidding any other repeat.  Note a
**loop** `D.Adj v v` counts as a directed cycle of length `1` under this
definition, which is what makes the acyclicity hypotheses below (`hacyc`)
automatically exclude loops — relied on by `exists_topological_ordering`. -/
def IsDirectedCycle {V : Type*} (D : Digraph V) {u : V} (p : @Quiver.Path V D.toQuiver u u) : Prop :=
  0 < (@Quiver.Path.length V D.toQuiver u u p) ∧
    (@Quiver.Path.vertices V D.toQuiver u u p).tail.Nodup

/-! ### Reachability — no `Quiver` instance needed, so `D` and `D.converse` coexist freely. -/

/-- `v` is **reachable** from `u`.

**Book definition** (B&M §10.1, verbatim).  *If there is a directed `(u, v)`-path in
`D`, vertex `v` is said to be reachable from vertex `u` in `D`.*

**Reading.**  You can get from `u` to `v` travelling only along arrows in their
given direction.  Reachability is *not* symmetric — that asymmetry is the whole
point of directing a graph, and is what makes diconnection a strictly stronger
condition than connection.

**Formalisation.**  `Relation.ReflTransGen D.Adj` rather than an existential over
`Quiver.Path`.  The two agree (a path witnesses reachability and conversely), but
`ReflTransGen` comes with induction principles and is *reflexive*, matching the
book's convention that every vertex reaches itself.  Being defined directly from
`Adj`, it needs no `Quiver` instance, so `D` and `D.converse` coexist freely —
which `converse_reachable` relies on. -/
def Reachable {V : Type*} (D : Digraph V) (u v : V) : Prop := Relation.ReflTransGen D.Adj u v

/-- `D` is **diconnected**: every vertex reaches every other.

**Book definition** (B&M §10.1, verbatim).  *Two vertices are diconnected in `D` if
each is reachable from the other.  As in the case of connection in graphs,
diconnection is an equivalence relation on the vertex set of `D`.  The subdigraphs
`D[V₁], D[V₂], …, D[V_m]` induced by the resulting partition `(V₁, V₂, …, V_m)` of
`V(D)` are called the dicomponents of `D`.  A digraph `D` is diconnected if it has
exactly one dicomponent.*

**Reading.**  Wherever you start and wherever you want to go, some route respecting
the arrows exists.  In the road-network reading of §10.6 this is exactly the
condition that a one-way system lets traffic flow freely — every junction remains
reachable from every other, and Robbins' theorem 10.5 says `2`-edge-connectivity is
precisely what makes it achievable.

**Formalisation.**  Stated directly as "every ordered pair is reachable" rather
than via dicomponents, which avoids constructing the quotient.  The two agree: one
dicomponent means the equivalence relation is total.  Note this is *not* symmetric
by fiat — `∀ u v, Reachable u v` quantifies over ordered pairs, so both directions
are demanded. -/
def Diconnected {V : Type*} (D : Digraph V) : Prop := ∀ u v : V, D.Reachable u v

/-! ### Degrees (⚠ MISSING — 0 hits in all of Mathlib). -/

/-- `d⁻(v)`, the **indegree**.

**Book definition** (B&M §10.1, verbatim).  *The indegree `d⁻_D(v)` of a vertex `v`
in `D` is the number of arcs with head `v`.*

**Reading.**  How many arrows point *into* `v`.  Exercise 10.1.2 gives the directed
handshake lemma `∑ d⁻(v) = ε = ∑ d⁺(v)` — each arc is counted once by its head and
once by its tail, which is why the directed sum is `ε` and not `2ε`.

**Formalisation.**  ⚠ Missing from Mathlib (0 hits).  Counts *vertices* `u` with
`D.Adj u v`, not arcs — the same thing here, since `Digraph` is a bare relation and
admits no parallel arcs.  Needs `[DecidableRel D.Adj]` for the `filter`. -/
def indegree {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj] (v : V) : ℕ :=
  (Finset.univ.filter fun u => D.Adj u v).card

/-- `d⁺(v)`, the **outdegree**.

**Book definition** (B&M §10.1, verbatim).  *…the outdegree `d⁺_D(v)` of `v` is the
number of arcs with tail `v`.*

**Reading.**  How many arrows point *out of* `v`.  Together with the indegree this
refines the single degree of an undirected graph into two numbers, and their
interplay drives most of the chapter: Euler tours need them equal (exercise
10.3.2), Ghouila-Houri's theorem 10.4 needs both large, and exercise 10.1.10 asks
for an orientation making them nearly equal everywhere.

**Formalisation.**  ⚠ Missing from Mathlib.  The exact mirror of `indegree` under
`converse`, which is the content of exercise 10.1.5(a)(ii). -/
def outdegree {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj] (v : V) : ℕ :=
  (Finset.univ.filter fun w => D.Adj v w).card

/-- `ε`, the number of **arcs**.

**Book convention** (B&M §10.1, verbatim).  *Throughout this chapter, `D` will
denote a digraph and `G` its underlying graph.  This is a useful convention; it
allows us, for example, to denote the vertex set of `D` by `V` (since
`V = V(G)`), and the numbers of vertices and arcs in `D` by `ν` and `ε`,
respectively.*

**Reading.**  Count the ordered pairs `(u, v)` for which an arc runs from `u` to
`v`.  This is the `ε` of exercise 10.1.2's handshake lemma and of exercise 10.1.1's
`2^ε` orientation count.

**Formalisation.**  Since `Digraph` allows no parallel arcs in the same direction,
`ε` is simply the size of the adjacency relation, counted as a `Finset (V × V)`.
Note this differs from the book for multi-digraphs, which B&M permit — a point that
also forces the restatement of `adjMatrix` below. -/
def arcCount {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj] : ℕ :=
  (Finset.univ.filter fun p : V × V => D.Adj p.1 p.2).card

/-- `δ⁻`, the minimum indegree.

**Book definition** (B&M §10.1, verbatim).  *We denote the minimum and maximum
indegrees and outdegrees in `D` by `δ⁻(D)`, `Δ⁻(D)`, `δ⁺(D)` and `Δ⁺(D)`,
respectively.*

**Reading.**  The least number of arrows pointing into any one vertex.  Exercise
10.1.3(a) says an acyclic digraph must have `δ⁻ = 0`, which is what makes
topological ordering possible; exercises 10.1.6–10.1.7 turn a large `δ⁻` into long
directed paths and cycles.

**Formalisation.**  ⚠ `⨅` over `ℕ` is `Nat.sInf`, and `Nat.sInf ∅ = 0`, so on an
empty carrier this silently returns `0` rather than being undefined.  Every use
site below carries `[Nonempty V]` for that reason.  Only the *minima* are defined
here; `Δ⁻`, `Δ⁺` are never needed by a surviving statement. -/
noncomputable def minIndegree {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj] : ℕ :=
  ⨅ v, D.indegree v

/-- `δ⁺`, the minimum outdegree.

**Book definition** (B&M §10.1).  The same sentence as for `δ⁻`: *We denote the
minimum and maximum indegrees and outdegrees in `D` by `δ⁻(D)`, `Δ⁻(D)`, `δ⁺(D)`
and `Δ⁺(D)`, respectively.*

**Reading.**  The least number of arrows leaving any one vertex.  By the converse
symmetry of exercise 10.1.5, statements about `δ⁻` transfer to `δ⁺` and back —
exactly how exercise 10.1.5(b) deduces `δ⁺ = 0` for acyclic digraphs from
`δ⁻ = 0`, without repeating the argument.

**Formalisation.**  Same `Nat.sInf ∅ = 0` caveat as `minIndegree`. -/
noncomputable def minOutdegree {V : Type*} [Fintype V] (D : Digraph V) [DecidableRel D.Adj] : ℕ :=
  ⨅ v, D.outdegree v

/-! ### Structural predicates (all ⚠ MISSING; all static). -/

/-- The **converse** `D̆`: reverse every arc.

**Book definition** (B&M exercise 10.1.5, verbatim).  *The converse `D̆` of `D` is
the digraph obtained from `D` by reversing the orientation of each arc.*

**Reading.**  Turn every arrow around.  It is an involution (`D̆̆ = D`), it swaps
indegree with outdegree, and it reverses reachability — so every theorem about
digraphs comes with a free dual, obtained by applying it to the converse.  Exercise
10.1.5(a) records exactly these three facts and (b) puts them to work.

**Formalisation.**  A one-line `Digraph.mk` with the arguments of `Adj` swapped, so
`converse_converse` should be `rfl`-adjacent.  Because `Reachable` is defined from
`Adj` and not through a `Quiver` instance, `D` and `D.converse` can appear in the
same statement without ambiguity — see `converse_reachable`. -/
def converse {V : Type*} (D : Digraph V) : Digraph V := ⟨fun u v => D.Adj v u⟩

/-- `D` is **strict**: loopless (`Digraph` already forbids parallel same-direction arcs).

**Book definition** (B&M §10.1, verbatim).  *A digraph is strict if it has no loops
and no two arcs with the same ends have the same orientation.*

**Reading.**  The directed analogue of "simple".  Note a strict digraph *may* have
both `(u,v)` and `(v,u)` — forbidding that is what makes an orientation, which is a
strictly stronger condition.  Strictness is the standing hypothesis of exercises
10.1.6, 10.1.7 and theorem 10.4, where it guarantees that `δ⁺` out-neighbours are
`δ⁺` genuinely *distinct* vertices.

**Formalisation.**  Since `Digraph` is a bare relation it already forbids repeated
arcs in the same direction, so the book's second clause is automatic and strictness
reduces to looplessness — `Irreflexive D.Adj`. -/
def IsStrict {V : Type*} (D : Digraph V) : Prop := Irreflexive D.Adj

/-- `D` is an **orientation** of `G` — the chapter's keystone gap.

**Book definition** (B&M §10.1, verbatim).  *With each digraph `D` we can associate
a graph `G` on the same vertex set; corresponding to each arc of `D` there is an
edge of `G` with the same ends.  This graph is the underlying graph of `D`.
Conversely, given any graph `G`, we can obtain a digraph from `G` by specifying,
for each link, an order on its ends.  Such a digraph is called an orientation of
`G`.*

**Reading.**  Make every edge one-way, choosing a direction for each.  Orientations
are the chapter's central object: exercise 10.1.1 counts them (`2^ε`), the remark
after theorem 10.1 builds one whose directed paths are short, exercise 10.1.10 one
that is degree-balanced, and §10.6 asks which graphs admit *diconnected* ones —
Robbins' theorem 10.5.

**Formalisation.**  Two clauses.  The first, `D.toSimpleGraphInclusive = G`, says
the underlying graph comes back out as `G`.  The second,
`∀ u v, ¬(D.Adj u v ∧ D.Adj v u)`, forbids making an edge two-way — without it the
associated digraph `D(G)` would count as an orientation of `G`, which it is not.
Taking `u = v` in the second clause also forces looplessness, so an orientation is
automatically strict. -/
def IsOrientationOf {V : Type*} (D : Digraph V) (G : SimpleGraph V) : Prop :=
  D.toSimpleGraphInclusive = G ∧ ∀ u v, ¬(D.Adj u v ∧ D.Adj v u)

/-- `D` is a **tournament**: an orientation of the complete graph.

**Book definition** (B&M §10.2, verbatim).  *An orientation of a complete graph is
called a tournament.  The tournaments on four vertices are shown in figure 10.4.
Each can be regarded as indicating the results of games in a round-robin tournament
between four players; for example, the first tournament in figure 10.4 shows that
one player has won all three games and that the other three have each won one.*

**Reading.**  Every pair of players meets exactly once and the arrow points from
winner to loser.  Tournaments are remarkably well behaved: every one has a directed
Hamilton path (Rédei, corollary 10.1) and a "king" reaching everyone in at most two
steps (corollary 10.2); diconnected ones are vertex-pancyclic (Moon, theorem 10.3)
and hence have directed Hamilton cycles (Camion).  §10.7 uses them to rank players.

**Formalisation.**  Unfolded rather than defined as "`IsOrientationOf` some
complete graph": `Irreflexive D.Adj` plus, for distinct `u`, `v`, exactly one of
`D.Adj u v`, `D.Adj v u`.  The `↔ ¬` phrasing packs both "at least one" (from
completeness of the underlying graph) and "at most one" (from being an orientation)
into a single clause. -/
def IsTournament {V : Type*} (D : Digraph V) : Prop :=
  Irreflexive D.Adj ∧ ∀ u v, u ≠ v → (D.Adj u v ↔ ¬ D.Adj v u)

/-- B&M's `(S, T)`: arcs with tail in `S`, head in `T`.

**Book definition** (B&M §10.3, verbatim).  *If `S` and `T` are subsets of `V`, we
denote by `(S, T)` the set of arcs of `D` that have their tails in `S` and their
heads in `T`.*

**Reading.**  The arcs crossing from `S` into `T`, counted with their direction.
Unlike the undirected edge cut `[S, S̄]`, the directed version splits into two
generally *unequal* halves `(S, S̄)` and `(S̄, S)` — which is precisely what
`k`-arc-connectivity measures, and what theorem 10.6 has to balance.

**Formalisation.**  A `Finset (V × V)` obtained by filtering the product `S ×ˢ T`,
so `|(S, T)|` is its `card`.  Used in `IsKArcConnected` and in Moon's theorem 10.3,
where the book's "`(S, T)` must be nonempty" becomes a cardinality claim. -/
def arcsBetween {V : Type*} (D : Digraph V) [DecidableRel D.Adj] (S T : Finset V) : Finset (V × V) :=
  (S ×ˢ T).filter fun p => D.Adj p.1 p.2

/-- `D` is **`k`-arc-connected**: every nonempty proper cut has `≥ k` outgoing arcs.

**Book definition** (B&M exercise 10.3.5, verbatim).  *A nontrivial digraph `D` is
`k`-arc-connected if, for every nonempty proper subset `S` of `V`,
`|(S, S̄)| ≥ k`.*

**Reading.**  However you split the vertices in two, at least `k` arrows point from
the first part to the second.  Exercise 10.3.5 says `1`-arc-connected is the same
as diconnected, and exercise 10.3.6(b) that `D(G)` is `k`-arc-connected exactly when
`G` is `k`-edge-connected.  Nash-Williams' theorem — of which theorem 10.6 is the
easy special case — says every `2k`-edge-connected graph has a `k`-arc-connected
orientation.

**Formalisation.**  ⚠ The book says **nontrivial** digraph, and this definition
drops that.  On a one-vertex carrier there is no nonempty proper `S`, so the
condition is vacuously true for *every* `k` — which is why statements consuming it
must supply `[Nontrivial V]` themselves.  `diconnected_iff_isKArcConnected_one`
does; `associatedDigraph_isKArcConnected_iff` does not, and is false in consequence
(see its docstring). -/
def IsKArcConnected {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (k : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k ≤ (D.arcsBetween S Sᶜ).card

/-- The **induced subdigraph** on `S` (kept on the same carrier to avoid subtype juggling).

**Book definition** (B&M §10.1, verbatim).  *A digraph `D'` is a subdigraph of `D`
if `V(D') ⊆ V(D)`, `A(D') ⊆ A(D)` and `ψ_{D'}` is the restriction of `ψ_D` to
`A(D')`.  The terminology and notation for subdigraphs is similar to that used for
subgraphs.*

**Reading.**  Keep only the vertices in `S` and the arcs with both ends there.  The
dicomponents of `D` are the induced subdigraphs `D[Vᵢ]` on the diconnection classes,
and theorem 10.2's induction removes `{v} ∪ N⁺(v)` this way.

**Formalisation.**  Kept on the **same carrier** `V`, with membership in `S` folded
into `Adj`, rather than moving to a subtype.  This avoids subtype juggling across
the many statements that induce, at the cost that `induce D S` has isolated
vertices outside `S` — harmless, since every consumer only asks about arcs. -/
def induce {V : Type*} (D : Digraph V) (S : Set V) : Digraph V :=
  ⟨fun u v => D.Adj u v ∧ u ∈ S ∧ v ∈ S⟩

/-! ### Extras billed to their single consumer. -/

/-- The list of arcs traversed by a directed walk.

**Book context** (B&M §10.1).  Implicit in the definition of a directed walk as the
sequence `(v₀, a₁, v₁, …, a_k, v_k)`: the `aᵢ` *are* this list.  The book never
names it, because its walks carry their arcs; `Quiver.Path` does not, so the list
has to be recovered.

**Reading.**  Reading off the arrows a directed walk uses, in order.  This is what a
*trail* condition quantifies over — a directed trail repeats no arc — and what a
directed Euler tour must exhaust.

**⚠ Defective: this definition has a `sorry` body.**  It is declared
`List (V × V) := sorry`, so `arcsOf` is an *opaque, unspecified* function, not the
arc list of anything.  This is the most damaging defect in the file, because the
opacity propagates:

* `IsDirectedTrail` and `IsDirectedEulerTour` are defined from it, so both are
  meaningless as stated;
* and therefore `exists_directedEulerTour_iff` (exercise 10.3.2),
  `deBruijnDigraph_exists_directedEulerTour` and `exists_arcDisjoint_directedPaths`
  (exercise 10.3.3) say nothing — which is the entire §10.5 computer-drum
  application plus the flow precursor to chapter 11.
* It also violates the project convention (`.claude/CLAUDE.md`): *never `sorry` in
  a `def`* — a `sorry`-ed proof is an honest debt, a `sorry`-ed definition is a
  silent change of meaning.

*The repair* is a routine structural recursion on `Quiver.Path`, whose two
constructors are `nil : Path a a` and `cons : Path a b → (b ⟶ c) → Path a c`:

    arcsOf nil        = []
    arcsOf (cons p e) = arcsOf p ++ [(b, c)]

with `b`, `c` the source and target of the arrow `e`.  Nothing about it is
delicate; the outline simply left it unspecified.  This is a change of *meaning*,
not of annotation, so it has been flagged rather than made here. -/
def arcsOf {V : Type*} (D : Digraph V) {u v : V} (p : @Quiver.Path V D.toQuiver u v) :
    List (V × V) := sorry

/-- A directed **trail**: no repeated arc.

**Book definition** (B&M §10.1, verbatim).  *A directed trail is a directed walk
that is a trail* — i.e. one whose arcs are all distinct.

**Reading.**  Follow the arrows, never using the same arrow twice, though you may
revisit vertices.  The directed analogue of §1.6's trail, and the notion an Euler
tour refines.

**Formalisation.**  ⚠ Inherits the `arcsOf` defect: since `arcsOf` is `sorry`, this
predicate is `(opaque list).Nodup` and means nothing.  Repairing `arcsOf` repairs
this automatically. -/
def IsDirectedTrail {V : Type*} (D : Digraph V) {u v : V} (p : @Quiver.Path V D.toQuiver u v) :
    Prop := (D.arcsOf p).Nodup

/-- A directed **Euler tour**: a closed directed trail using every arc.

**Book definition** (B&M exercise 10.3.2, verbatim).  *A directed Euler tour of `D`
is a directed tour that traverses each arc of `D` exactly once.*

**Reading.**  The directed version of Euler's problem — traverse every one-way
street exactly once and return to the start.  Exercise 10.3.2 gives the criterion:
possible exactly when `D` is connected and `d⁺(v) = d⁻(v)` everywhere, the directed
analogue of theorem 4.1's even-degree condition, because every visit uses one arrow
in and one out.  §10.5 uses it to design an efficient computer drum via the de
Bruijn digraph.

**⚠ Defective on two counts.**
1. *Inherits the `arcsOf` defect* — both conjuncts are stated in terms of an opaque
   function, so the predicate currently means nothing.
2. *Admits the null walk.*  B&M's directed walks are explicitly **non-null**
   (§10.1), so `nil` is not a directed tour for them; here `Quiver.Path.nil`
   satisfies both conjuncts vacuously (`[].Nodup`, and no arc to exhaust when `D`
   has none).  This is not cosmetic: it makes `exists_directedEulerTour_iff` false
   outright — see the counterexample there.

*The repair* for (2) is to add `0 < Quiver.Path.length p`, matching "non-null".
Both repairs change *meaning*, so they are flagged rather than made here. -/
def IsDirectedEulerTour {V : Type*} (D : Digraph V) {u : V} (p : @Quiver.Path V D.toQuiver u u) :
    Prop := D.IsDirectedTrail p ∧ ∀ a b : V, D.Adj a b → (a, b) ∈ D.arcsOf p

/-- `D` is **unilateral**: any two vertices are comparable by reachability.

**Book definition** (B&M exercise 10.2.2, verbatim).  *A digraph `D` is unilateral
if, for any two vertices `u` and `v`, either `v` is reachable from `u` or `u` is
reachable from `v`.*

**Reading.**  Weaker than diconnected — you need only get *one* way between any two
vertices, not both.  Exercise 10.2.2 characterises it: `D` is unilateral exactly
when it has a spanning directed *walk*.

**Formalisation.**  The disjunction is over `Reachable`, which is reflexive, so the
case `u = v` is automatic.  Note "unilateral" sits strictly between "connected"
(underlying graph) and "diconnected". -/
def IsUnilateral {V : Type*} (D : Digraph V) : Prop :=
  ∀ u v : V, D.Reachable u v ∨ D.Reachable v u

/-- The 0/1 **adjacency matrix** of `D`. ⚠ RESTATED: `Digraph` has no arc multiplicities.

**Book definition** (B&M exercise 10.1.8, verbatim).  *Let `v₁, v₂, …, v_ν` be the
vertices of a digraph `D`.  The adjacency matrix of `D` is the `ν × ν` matrix
`A = [a_ij]` in which `a_ij` is the number of arcs of `D` with tail `vᵢ` and head
`vⱼ`.*

**Reading.**  Record a `1` where an arrow runs from `vᵢ` to `vⱼ` and `0` otherwise.
Unlike the undirected case (§1.3) this matrix is *not* symmetric — its asymmetry
encodes the orientations.  Exercise 10.1.8 shows `Aᵏ` counts directed walks of
length `k`, and §10.7 uses the powers of `A` to rank tournament players via the
level score vectors `sᵢ = AⁱJ`.

**Formalisation.**  ⚠ Restated: `Digraph` has no arc multiplicities, so entries are
`0` or `1` rather than a count.  For strict digraphs — which every §10.7 statement
is about, tournaments being orientations — the two agree, so nothing is lost where
it is used.  The value type `α` is left generic so the same matrix serves the
ℕ-valued counting of exercise 10.1.8 and any later numeric work. -/
def adjMatrix {V : Type*} (D : Digraph V) [DecidableRel D.Adj] (α : Type*) [Zero α] [One α] :
    Matrix V V α := Matrix.of fun u v => if D.Adj u v then 1 else 0

/-- The **condensation** `D̂`: dicomponents contracted. ⚠ the `a ≠ b` clause is a recorded correction
(B&M's literal statement is false — an internal arc would give a loop).

**Book definition** (B&M exercise 10.1.9, verbatim).  *Let `D₁, D₂, …, D_m` be the
dicomponents of `D`.  The condensation `D̂` of `D` is a directed graph with `m`
vertices `w₁, w₂, …, w_m`; there is an arc in `D̂` with tail `wᵢ` and head `wⱼ` if
and only if there is an arc in `D` with tail in `Dᵢ` and head in `Dⱼ`.*

**Reading.**  Shrink each dicomponent to a single point and keep the arcs between
them.  Exercise 10.1.9 shows the condensation is *acyclic* — a directed cycle among
dicomponents would merge them into one — so by exercise 10.1.3(b) the dicomponents
can be topologically ordered, which is what §10.7 uses to rank the participants of a
non-diconnected tournament, and what exercise 10.2.1 uses on tournaments.

**Formalisation.**  ⚠ The `a ≠ b` clause is a **recorded correction**, not a
transcription.  Taken literally the book's condition puts an arc from `wᵢ` to `wᵢ`
whenever `Dᵢ` has any internal arc — a loop at every non-trivial dicomponent — which
would make `condensation_acyclic` false, since a loop is a directed cycle of length
`1`.  B&M plainly intend `i ≠ j`.

The vertex type is `Quiver.StronglyConnectedComponent`, Mathlib's quotient by mutual
reachability, which is exactly the set of dicomponents. -/
def condensation {V : Type*} (D : Digraph V) :
    Digraph (@Quiver.StronglyConnectedComponent V D.toQuiver) :=
  ⟨fun a b => a ≠ b ∧ ∃ u v : V, D.Adj u v ∧
    (@Quiver.StronglyConnectedComponent.mk V D.toQuiver u) = a ∧
    (@Quiver.StronglyConnectedComponent.mk V D.toQuiver v) = b⟩

/-- **Directed distance** `d⃗(u,v)`. ⚠ `Nat.sInf ∅ = 0` when `v` is unreachable from `u`.

**Book definition** (B&M §10.7, verbatim).  *In a diconnected digraph `D`, the
length of a shortest directed `(u, v)`-path is denoted by `d⃗_D(u, v)` and is called
the distance from `u` to `v`; the directed diameter of `D` is the maximum distance
from any one vertex of `D` to any other.*

**Reading.**  The fewest arrows you must follow to get from `u` to `v`.  Unlike the
undirected distance of §1.6 this is *not symmetric* — `d⃗(u,v)` and `d⃗(v,u)` may
differ, which is the whole reason §10.7 needs `d + 3` rather than something
symmetric.

**Formalisation.**  ⚠ `Nat.sInf ∅ = 0`, so an unreachable `v` gets distance `0`
rather than `∞`.  The definition is therefore faithful only on diconnected
digraphs — which is exactly where the book defines it, and both consumers
(`tournament_adjMatrix_pow_pos`, `dirDiameter`) carry `hdicon`.  Minimising over
`Quiver.Path` lengths rather than over `Reachable` witnesses, since the *length* is
what is wanted. -/
noncomputable def dirDist {V : Type*} (D : Digraph V) (u v : V) : ℕ :=
  sInf {n | ∃ p : @Quiver.Path V D.toQuiver u v, @Quiver.Path.length V D.toQuiver u v p = n}

/-- **Directed diameter**.

**Book definition** (B&M §10.7, verbatim).  *…the directed diameter of `D` is the
maximum distance from any one vertex of `D` to any other.*

**Reading.**  The worst case of the directed distance — how far apart two vertices
can be when you must respect the arrows.  Theorem 10.7 shows that for a diconnected
tournament on at least five vertices `A^{d+3}` is entrywise positive, where `d` is
this diameter, and corollary 10.7 turns that into the primitivity that makes the
§10.7 ranking method converge.

**Formalisation.**  A `Finset.sup` over all ordered pairs, so the diagonal `d⃗(v,v) = 0`
is included harmlessly.  Inherits `dirDist`'s `sInf ∅ = 0` caveat: on a
non-diconnected digraph the diameter is silently too small. -/
noncomputable def dirDiameter {V : Type*} [Fintype V] (D : Digraph V) : ℕ :=
  Finset.univ.sup fun p : V × V => D.dirDist p.1 p.2

end Digraph

/-! ## Consumer-specific definitions on other carriers -/

/-- The **associated digraph** `D(G)`: each edge becomes two opposite arcs.  `G.Adj` is already
symmetric, so it *is* the arc relation.

**Book definition** (B&M exercise 10.3.6, verbatim).  *The associated digraph `D(G)`
of a graph `G` is the digraph obtained when each edge `e` of `G` is replaced by two
oppositely oriented arcs with the same ends as `e`.*

**Reading.**  Make every street two-way.  This embeds undirected graph theory inside
directed graph theory: exercise 10.3.6 shows paths in `G` correspond exactly to
directed paths in `D(G)`, and `D(G)` is `k`-arc-connected exactly when `G` is
`k`-edge-connected.  Exercise 10.3.1 uses the embedding to derive Dirac's theorem
4.3 from Ghouila-Houri's 10.4.

**Formalisation.**  One line: `G.Adj` is already symmetric and irreflexive, so it
*is* the arc relation of `D(G)` — the "two oppositely oriented arcs" are the two
directions of the symmetric relation.  Note `D(G)` is emphatically **not** an
orientation of `G` (`IsOrientationOf`'s second clause fails at every edge); the
contrast between doubling and orienting is exactly what §10.6 is about. -/
def SimpleGraph.associatedDigraph {V : Type*} (G : SimpleGraph V) : Digraph V := ⟨G.Adj⟩

/-- A **primitive** ℕ-matrix: some power is entrywise positive. ⚠ MISSING (0 hits).

**Book definition** (B&M §10.7, verbatim).  *A real matrix `R` is called primitive
if `Rᵏ > 0` for some `k`.*

**Reading.**  For the adjacency matrix this says: however you pick a starting and
finishing vertex, there is a directed walk of some *common* length `k` between them.
Corollary 10.7 characterises when a tournament's matrix is primitive — exactly when
the tournament is diconnected with `ν ≥ 4`.  Primitivity is what licenses
Perron–Frobenius, which gives the convergence of the iterated score vectors
`sᵢ = AⁱJ` used to rank the players.

**Formalisation.**  ⚠ Missing from Mathlib (0 hits).  Stated for `Matrix n n ℕ`
rather than the book's *real* matrices, since the only instance needed is the
adjacency matrix; `0 < (R ^ k) i j` is then the entrywise positivity `Rᵏ > 0`.  Note
Mathlib's `Matrix` order is not entrywise by default, which is why the positivity is
spelled pointwise. -/
def Matrix.IsPrimitive {n : Type*} [Fintype n] [DecidableEq n] (R : Matrix n n ℕ) : Prop :=
  ∃ k : ℕ, ∀ i j, 0 < (R ^ k) i j

/-- The **de Bruijn digraph** `D_n`: vertices are `(n-1)`-bit strings, arcs are left-shifts.
⚠ MISSING (0 hits in Mathlib or Archive); `D_n` has loops but no parallel arcs.

**Book definition** (B&M §10.5, verbatim).  *We define a digraph `D_n` as follows:
the vertices of `D_n` are the `(n-1)`-digit binary numbers `p₁ p₂ … p_{n-1}` with
`pᵢ = 0` or `1`.  There is an arc with tail `p₁ p₂ … p_{n-1}` and head
`q₁ q₂ … q_{n-1}` if and only if `p_{i+1} = qᵢ` for `1 ≤ i ≤ n-2`; in other words,
all arcs are of the form `(p₁ p₂ … p_{n-1}, p₂ p₃ … p_n)`.  In addition, each arc
`(p₁ p₂ … p_{n-1}, p₂ p₃ … p_n)` of `D_n` is assigned the label `p₁ p₂ … p_n`.*

**Reading.**  A vertex is a window of `n-1` bits; following an arc shifts the window
one place, dropping the leading bit and appending a new one.  Each arc therefore
corresponds to an `n`-bit string — its label — and a directed Euler tour reads off
every `n`-bit string exactly once, giving a cyclic binary sequence of length `2ⁿ` in
which all `2ⁿ` windows are distinct.

*The application (§10.5).*  A rotating drum's surface is divided into `2ⁿ`
insulating or conducting sections, read by `k` consecutive contacts.  *First note
that `k` contacts yield a `k`-digit binary number, and there are `2ᵏ` such numbers.
Therefore, if all `2ⁿ` positions are to give different readings, we must have
`2ᵏ ≥ 2ⁿ`, that is, `k ≥ n`* — and the de Bruijn sequence shows `n` contacts
suffice.  For `n = 4` the tour of figure 10.10 gives `0000111100101101`.  Due to
Good (1946).

**Formalisation.**  ⚠ Missing from Mathlib and the Archive (0 hits).  A vertex is a
function `Fin (n-1) → Bool` rather than a list, so the shift condition is indexed:
`p ⟨i+1, _⟩ = q i` for every `i` with `i + 1 < n - 1`, which is the book's
`1 ≤ i ≤ n-2` in 0-indexed form.  The last coordinate of `q` is unconstrained, giving
the two out-arcs.  `D_n` has **loops** (the all-zeros and all-ones vertices) but no
parallel arcs — so it is not strict, which is fine, as no §10.5 statement needs
strictness.  Arc labels are not modelled: the label is recoverable from the arc, and
`exists_deBruijn_sequence` states the conclusion about the sequence directly. -/
def deBruijnDigraph (n : ℕ) : Digraph (Fin (n - 1) → Bool) :=
  ⟨fun p q => ∀ i : Fin (n - 1), (h : (i : ℕ) + 1 < n - 1) → p ⟨(i : ℕ) + 1, h⟩ = q i⟩

/-! ## §10.1 -/

-- Ex 10.1.1: a simple graph has `2^ε` orientations.
/-- **Exercise 10.1.1** (B&M §10.1, verbatim).  *How many orientations does a simple
graph `G` have?*

**Book proof.**  None — an exercise, and one posed as a question, so the answer
`2^ε` is itself part of what must be supplied.

**Skeleton** (for `Nat.card {D : Digraph V // D.IsOrientationOf G} = 2 ^ ε`).
1. **Build the bijection with edge-labellings.**  An orientation is exactly a choice
   of direction per edge, so construct

       {D : Digraph V // D.IsOrientationOf G} ≃ (G.edgeFinset → Bool)

   *Forwards:* given `D` and an edge `s(u,v)`, record which of `D.Adj u v`,
   `D.Adj v u` holds — well defined by `IsOrientationOf`'s second clause (not both)
   and its first (at least one, since the edge is in the underlying graph).  The
   `Sym2` needs `Sym2.lift` plus a proof the choice is symmetric under swapping.
   *Backwards:* given `f`, define `Adj u v` to hold when `G.Adj u v` and `f`
   selects the `u → v` direction at `s(u,v)`.  Then verify both clauses of
   `IsOrientationOf`.
2. Round trips: both are extensionality arguments on `Digraph.Adj` and on
   functions out of `edgeFinset`.
3. `Nat.card (α → Bool) = 2 ^ Nat.card α` for a finite `α`, then rewrite
   `Nat.card G.edgeFinset = G.edgeFinset.card`.

**Reading.**  An orientation is a choice, independently for each edge, of one of its
two directions; with `ε` edges and two choices each the product rule gives `2^ε`.
These are *labelled* objects: two orientations differing only by a symmetry of `G`
still count separately.

**Formalisation.**  Step 1 is the whole exercise and the `Sym2` bookkeeping is the
only fiddly part — the natural first move is to prove a helper turning
`IsOrientationOf` into "for each edge, exactly one of the two directions". -/
theorem card_orientations
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nat.card {D : Digraph V // D.IsOrientationOf G} = 2 ^ G.edgeFinset.card := by
  sorry

-- Ex 10.1.2: the directed handshake lemma `∑ d⁻ = ε = ∑ d⁺`.
/-- **Exercise 10.1.2** (B&M §10.1, verbatim).  *Show that
`∑_{v∈V} d⁻(v) = ε = ∑_{v∈V} d⁺(v)`.*

**Book proof.**  None — an exercise.

**Skeleton** (for the conjunction `∑ indegree = arcCount ∧ ∑ outdegree = arcCount`).
1. **Both halves are one double-counting lemma.**  `arcCount` is the card of
   `univ.filter fun p : V × V => D.Adj p.1 p.2`, a `Finset (V × V)`.
2. **Indegree half.**  Partition that filter by its *second* coordinate:
   `Finset.card_eq_sum_card_fiberwise` with the fibre map `p ↦ p.2` gives
   `arcCount = ∑ v, |{p ∈ filter | p.2 = v}|`, and the `v`-fibre is in bijection
   with `univ.filter fun u => D.Adj u v`, i.e. `indegree v`.
3. **Outdegree half.**  The same with `p ↦ p.1` and `outdegree`.
4. Both rewrites are the same lemma applied along the two projections, so factor
   the fibre-counting step out and instantiate it twice.

**Reading.**  The directed handshaking lemma.  Every arc has exactly one head, so
summing indegrees counts each arc once; likewise every arc has one tail.  Contrast
the undirected version (theorem 1.1), where the sum of degrees is `2ε`: there each
edge is counted twice, once from each end, whereas here the head-count and
tail-count are kept separate and each totals `ε`.

**Formalisation.**  Stated as a conjunction because the book states both equalities
at once; nothing forces them to share a proof, but step 4 notes they should. -/
theorem sum_indegree_eq_arcCount
    {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj] :
    (∑ v, D.indegree v) = D.arcCount ∧ (∑ v, D.outdegree v) = D.arcCount := by
  sorry

-- Ex 10.1.3(a): a digraph with no directed cycle has a vertex of indegree 0.
/-- **Exercise 10.1.3(a)** (B&M §10.1, verbatim).  *Let `D` be a digraph with no
directed cycle.  (a) Show that `δ⁻ = 0`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `∃ v, D.indegree v = 0`).
1. `by_contra`; then every vertex has `indegree v ≠ 0`, i.e. an in-neighbour.
2. **Build an infinite backwards walk.**  Using choice on step 1, define
   `f : ℕ → V` with `D.Adj (f (n+1)) (f n)` — from any start, always step back
   along an incoming arc.
3. **Pigeonhole.**  `V` is a `Fintype`, so `f` is not injective on
   `Fin (card V + 1)`: there are `i < j` with `f i = f j`.
4. **Extract the cycle.**  The segment `f j → f (j-1) → … → f i` is a closed
   directed walk of positive length.  Reduce it to a *directed cycle* — take `i`,
   `j` with `j - i` minimal among repeats, so no vertex recurs strictly inside,
   giving `vertices.tail.Nodup`.
5. Contradicts `hacyc`.

**Reading.**  If every vertex had an incoming arc one could walk backwards for ever;
finiteness forces a repeat, and the portion between the two visits is a directed
cycle.  So an acyclic digraph always has a "source" with nothing pointing into it —
the base of the topological-ordering induction in part (b).

**Formalisation.**  `[Nonempty V]` is load-bearing: on an empty carrier there is no
`v` to produce, while `hacyc` holds vacuously.  Note `hacyc` also rules out loops,
since a loop is a directed cycle of length `1` under `IsDirectedCycle`. -/
theorem exists_indegree_zero_of_acyclic
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (hacyc : ∀ (u : V) (p : @Quiver.Path V D.toQuiver u u), ¬ D.IsDirectedCycle p) :
    ∃ v : V, D.indegree v = 0 := by
  sorry

-- Ex 10.1.3(b): an acyclic digraph admits a topological ordering.
/-- **Exercise 10.1.3(b)** (B&M §10.1, verbatim).  *(b) Deduce that there is an
ordering `v₁, v₂, …, v_ν` of `V` such that, for `1 ≤ i ≤ ν`, every arc of `D` with
head `vᵢ` has its tail in `{v₁, v₂, …, v_{i-1}}`.*

**Book proof.**  None — an exercise; "deduce" points at part (a).

**Skeleton** (for `∃ f : V ≃ Fin (card V), ∀ u v, D.Adj u v → f u < f v`).
1. **Strong induction on `card V`**, generalising over the carrier: the recursive
   call is about `D.induce {v}ᶜ`, a digraph on a smaller vertex set.
2. **Base.**  `card V = 0`: the empty equivalence.
3. **Step.**  Part (a) gives `v₁` with `indegree v₁ = 0`.  The induced subdigraph on
   `{v₁}ᶜ` is still acyclic (a directed cycle there is one in `D`), so the induction
   hypothesis orders it.
4. **Extend.**  Place `v₁` first and shift the rest up by one.  Arcs into `v₁` do not
   exist (indegree `0`), and arcs out of `v₁` go to later vertices by construction;
   arcs among the rest are handled by the induction hypothesis.
5. Assemble the `Equiv` — this is where most of the Lean effort goes, since
   `V ≃ Fin (card V)` must be built by hand from the smaller equivalence.

**Reading.**  A **topological ordering**: line the vertices up so every arrow points
forwards.  Greedy construction via part (a) — take a source, delete it, repeat.
These are the standard tool for scheduling tasks with prerequisites, and §10.7 uses
the version for the *condensation* of a tournament to order its dicomponents in a
way that preserves dominance.

**Formalisation.**  The book's "every arc with head `vᵢ` has its tail among the
earlier vertices" is contraposed into the equivalent and more usable
`D.Adj u v → f u < f v`.  Note no `[Nonempty V]` is needed here, unlike part (a) —
the empty case is the induction's base. -/
theorem exists_topological_ordering
    {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (hacyc : ∀ (u : V) (p : @Quiver.Path V D.toQuiver u u), ¬ D.IsDirectedCycle p) :
    ∃ f : V ≃ Fin (Fintype.card V), ∀ u v : V, D.Adj u v → f u < f v := by
  sorry

-- DROPPED: Ex 10.1.4 (diconnected ⇔ connected ∧ every block diconnected) — BLOCKED: needs a block
-- decomposition absent from Mathlib and the repo; ch4's faked `IsBlock` was deleted.

-- Ex 10.1.5(a)(i): the converse is an involution.
/-- **Exercise 10.1.5(a)(i)** (B&M §10.1, verbatim).  *Show that (i) `D̆̆ = D`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `D.converse.converse = D`).
1. `Digraph.ext` reduces to equality of the `Adj` relations.
2. `funext u v` then unfolds `converse` twice: `(fun u v => (fun a b => D.Adj b a) v u)`
   beta-reduces to `D.Adj u v`.
3. Likely closed by `rfl` or `by ext u v; rfl`; if `Digraph.ext` is stated via
   `Adj` propositional extensionality, add `Iff.rfl`.

**Reading.**  Reversing every arrow twice returns each to its original direction, so
the converse is an involution.  That is what makes it a genuine duality: any
statement proved for all digraphs yields its mirror image for free, with in- and
outdegrees and the direction of reachability exchanged — as parts (ii), (iii) and
(b) then exploit.

**Formalisation.**  The shortest item in the file; a good first fill to shake out the
`Digraph` extensionality API. -/
theorem converse_converse {V : Type*} (D : Digraph V) : D.converse.converse = D := by
  sorry

open scoped Classical in
-- Ex 10.1.5(a)(ii): the converse swaps in/outdegree.
/-- **Exercise 10.1.5(a)(ii)** (B&M §10.1, verbatim).  *(ii) `d^±_{D̆}(v) = d^∓_D(v)`.*

**Book proof.**  None — an exercise.

**Skeleton** (for the conjunction
`converse.indegree v = outdegree v ∧ converse.outdegree v = indegree v`).
1. Unfold both sides to `Finset.card` of filters:
   `converse.indegree v = |univ.filter fun u => D.converse.Adj u v|` and
   `D.converse.Adj u v` is by definition `D.Adj v u`.
2. So the filter is `univ.filter fun u => D.Adj v u`, which is literally
   `outdegree v`'s filter — the two are equal as `Finset`s, so `rfl`-adjacent once
   the `DecidableRel` instances are reconciled.
3. **The likely friction is decidability**, not mathematics: `D.converse`'s
   `DecidableRel` instance is derived separately from `D`'s, so the two filters may
   not be syntactically equal.  `Finset.filter_congr_decidable` or
   `simp [converse, indegree, outdegree]` should bridge it.
4. Second conjunct symmetric.

**Reading.**  An arc pointing into `v` in `D` points out of `v` in the converse, and
vice versa.  This is the workhorse of the duality: exercise 10.1.5(b) uses it to
turn "acyclic ⟹ `δ⁻ = 0`" into "acyclic ⟹ `δ⁺ = 0`" without repeating the
argument.

**Formalisation.**  The `open scoped Classical in` on this declaration supplies
decidability for `D.converse.Adj`; step 3 is where that shows up. -/
theorem converse_indegree {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) [DecidableRel D.Adj] (v : V) :
    D.converse.indegree v = D.outdegree v ∧ D.converse.outdegree v = D.indegree v := by
  sorry

-- Ex 10.1.5(a)(iii): reachability reverses under the converse.
/-- **Exercise 10.1.5(a)(iii)** (B&M §10.1, verbatim).  *(iii) `v` is reachable from
`u` in `D̆` if and only if `u` is reachable from `v` in `D`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `D.converse.Reachable u v ↔ D.Reachable v u`).
1. Both sides are `Relation.ReflTransGen`; the statement is exactly
   `ReflTransGen (flip D.Adj) u v ↔ ReflTransGen D.Adj v u`.
2. Search Mathlib first: `Relation.reflTransGen_swap` (or
   `ReflTransGen.swap`) states precisely this and would close the goal after
   unfolding `converse`.
3. Failing that, prove each direction by `ReflTransGen.head_induction_on` /
   `ReflTransGen.trans`: a chain `u → … → v` in the converse is the reversed chain
   `v → … → u` in `D`, built by induction with `ReflTransGen.tail` becoming
   `ReflTransGen.head`.

**Reading.**  A directed path from `u` to `v` in the converse is exactly a directed
path from `v` to `u` in `D`, read backwards.  A useful consequence: diconnection is
*self-dual* — `D` is diconnected exactly when `D̆` is — since diconnection demands
reachability both ways.

**Formalisation.**  This is the one place where defining `Reachable` as
`ReflTransGen` rather than via `Quiver.Path` pays off directly: no `Quiver` instance
is in play, so `D` and `D.converse` appear in the same statement without
ambiguity. -/
theorem converse_reachable {V : Type*} (D : Digraph V) (u v : V) :
    D.converse.Reachable u v ↔ D.Reachable v u := by
  sorry

-- Ex 10.1.5(b): an acyclic digraph has a vertex of outdegree 0.
/-- **Exercise 10.1.5(b)** (B&M §10.1, verbatim).  *(b) By using part (ii) of (a),
deduce from exercise 10.1.3(a) that if `D` is a digraph with no directed cycle,
then `δ⁺ = 0`.*

**Book proof.**  None — an exercise, but the route is prescribed: via (a)(ii) from
10.1.3(a).

**Skeleton** (for `∃ v, D.outdegree v = 0`).
1. **`D.converse` is acyclic.**  Prove the transport lemma: a directed cycle in
   `D.converse` reverses to one in `D`.  Concretely, map a `Quiver.Path` in
   `D.converse` to a reversed one in `D`, checking `IsDirectedCycle` is preserved
   (length is preserved; `vertices.tail.Nodup` survives reversal).  *This is the
   only real work in the exercise*, and it does not appear in the book's hint.
2. Apply `exists_indegree_zero_of_acyclic` to `D.converse`, obtaining `v` with
   `D.converse.indegree v = 0`.
3. `converse_indegree` — part (a)(ii) — rewrites that to `D.outdegree v = 0`.

**Reading.**  An acyclic digraph has both a "source" (nothing in) and a "sink"
(nothing out), which is what lets topological ordering be built from either end.
The point of the exercise is methodological: the converse converts one statement
into its dual with no new argument.

**Formalisation.**  Step 1 needs a `Quiver.Path` reversal for `D.converse` versus
`D`; since `toQuiver` is not an instance, both quivers must be named explicitly.
Worth extracting as a standalone lemma, as `converse_reachable` is the same fact one
level down. -/
theorem exists_outdegree_zero_of_acyclic
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (hacyc : ∀ (u : V) (p : @Quiver.Path V D.toQuiver u u), ¬ D.IsDirectedCycle p) :
    ∃ v : V, D.outdegree v = 0 := by
  sorry

-- Ex 10.1.6: a strict digraph has a directed path of length `≥ max{δ⁻, δ⁺}`.
/-- **Exercise 10.1.6** (B&M §10.1, verbatim).  *Show that if `D` is strict, then `D`
contains a directed path of length at least `max{δ⁻, δ⁺}`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `∃ u v p, IsDirectedPath p ∧ max δ⁻ δ⁺ ≤ p.length`).
1. **Take a longest directed path.**  Directed paths have `Nodup` vertices, so their
   lengths are bounded by `card V`; with `[Nonempty V]` the set is nonempty (the
   `nil` path), so a maximum is attained.  Fix `P` with terminus `v`.
2. **Maximality confines the out-neighbours.**  Every out-neighbour of `v` lies on
   `P` — otherwise `cons P e` is a longer directed path.
3. **Count.**  Strictness makes the `outdegree v ≥ δ⁺` out-neighbours genuinely
   distinct vertices, all on `P` and all `≠ v` (no loops).  So `P` has at least
   `δ⁺` vertices besides `v`, i.e. `length P ≥ δ⁺`.
4. **The `δ⁻` half by duality.**  Apply steps 1–3 to `D.converse` — strict, with
   `δ⁺(D̆) = δ⁻(D)` by exercise 10.1.5(a)(ii) — and reverse the resulting path, using
   the transport lemma from 10.1.5(b) step 1.
5. `max` of the two bounds: note the *same* path need not achieve both, so the
   existential must be instantiated with whichever of the two paths is longer.

**Reading.**  The directed analogue of exercise 1.6.3.  Strictness is what makes the
counting work: it guarantees the out-neighbours are `δ⁺` genuinely distinct
vertices.

**Formalisation.**  ⚠ Step 5 is easy to get wrong.  The statement asks for **one**
path of length `≥ max{δ⁻, δ⁺}`, not one path per bound; since `max` is one of the
two, produce the two paths and pick the longer.  `minIndegree`/`minOutdegree` are
`⨅` over `ℕ`, so `[Nonempty V]` is needed to keep them from collapsing to `0`. -/
theorem exists_directedPath_length_ge_maxMinDegree
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (hstrict : D.IsStrict) :
    ∃ (u v : V) (p : @Quiver.Path V D.toQuiver u v),
      D.IsDirectedPath p ∧ max D.minIndegree D.minOutdegree ≤ @Quiver.Path.length V D.toQuiver u v p := by
  sorry

-- Ex 10.1.7: strict with `max{δ⁻,δ⁺} = k > 0` ⇒ a directed cycle of length `≥ k+1`.
/-- **Exercise 10.1.7** (B&M §10.1, verbatim).  *Show that if `D` is strict and
`max{δ⁻, δ⁺} = k > 0`, then `D` contains a directed cycle of length at least
`k + 1`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `∃ u p, IsDirectedCycle p ∧ k + 1 ≤ p.length`).
1. As in exercise 10.1.6, take a longest directed path `P = v₀v₁ … v_m` with
   terminus `v_m`, and note every out-neighbour of `v_m` lies on `P`.
2. **Close a cycle at the earliest out-neighbour.**  Let `vᵢ` be the out-neighbour
   of `v_m` with least index `i`.  Then the section `vᵢ … v_m` followed by the arc
   `v_m → vᵢ` is a closed directed walk; its vertices are distinct (a sub-path of
   `P`), so it is a directed cycle.
3. **Length count.**  All `≥ k` out-neighbours of `v_m` sit among
   `v_i, v_{i+1}, …, v_{m-1}` by minimality of `i`, and they are distinct by
   strictness, so `m - i ≥ k`.  The cycle has length `m - i + 1 ≥ k + 1`.
4. If `max` is achieved by `δ⁻` rather than `δ⁺`, run the whole argument on
   `D.converse` and reverse, as in exercise 10.1.6 step 4.

**Reading.**  Sharpens exercise 10.1.6 from paths to cycles, exactly as exercise
1.7.3 sharpens 1.6.3 undirected.  It is consumed inside Ghouila-Houri's theorem
10.4, which opens by noting `l > ν/2` for the longest directed cycle — that is this
exercise with `k ≥ ν/2`.

**Formalisation.**  `hk : 0 < k` is load-bearing: with `k = 0` the conclusion would
demand a directed cycle of length `≥ 1` in a digraph that may have no cycle at all.
`hdeg` pins `max δ⁻ δ⁺` to `k` as an equality, matching the book. -/
theorem exists_directedCycle_length_ge
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (hstrict : D.IsStrict) {k : ℕ} (hk : 0 < k)
    (hdeg : max D.minIndegree D.minOutdegree = k) :
    ∃ (u : V) (p : @Quiver.Path V D.toQuiver u u),
      D.IsDirectedCycle p ∧ k + 1 ≤ @Quiver.Path.length V D.toQuiver u u p := by
  sorry

-- Ex 10.1.8: `A^k` counts directed walks of length `k` (RESTATED: 0/1 matrix, no multiplicities).
/-- **Exercise 10.1.8** (B&M §10.1, verbatim).  *Show that the `(i, j)`th entry of
`Aᵏ` is the number of directed `(vᵢ, vⱼ)`-walks of length `k` in `D`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `(D.adjMatrix ℕ ^ k) u v = Nat.card {p : Path u v // p.length = k}`).
1. **Induct on `k`.**
2. **Base `k = 0`.**  `A⁰ = 1`, so the entry is `1` if `u = v` and `0` otherwise.
   On the right, the only path of length `0` is `nil`, which exists exactly when
   `u = v` — so the fibre is a singleton or empty.
3. **Step.**  `A^{k+1} = A^k * A`, so the entry is `∑ m, (A^k) u m * A m v`.  By the
   induction hypothesis this is `∑ m, |{p : Path u m // length = k}| * [D.Adj m v]`.
4. **The bijection.**  Paths `u → v` of length `k+1` are exactly `cons p e` for
   `p : Path u m` of length `k` and `e : m ⟶ v` — i.e.
   `{p : Path u v // length = k+1} ≃ Σ m, {p : Path u m // length = k} × PLift (D.Adj m v)`.
   This is `Quiver.Path`'s `cons` constructor being injective with decidable image;
   `Nat.card` of the sigma is the sum in step 3.
5. Note the `A m v` factor is `0` or `1` here, so the product is a *filter*, not a
   multiplicity — which is where the restatement below matters.

**Reading.**  The `(i,j)` entry of `A` counts arcs, i.e. walks of length one; matrix
multiplication sums over an intermediate vertex, and every walk of length `k`
decomposes uniquely as a shorter walk plus a final arc.  This is the directed
counterpart of exercise 1.6.2, and it is what makes §10.7's ranking work: the
`i`-th level score vector is `AⁱJ`, counting directed walks of length `i` out of
each player.  Theorem 10.7 consumes it directly.

**Formalisation.**  ⚠ Restated for a `0/1` matrix, `Digraph` having no arc
multiplicities; for the strict digraphs of §10.7 this is no loss.  The right-hand
side is `Nat.card` of a subtype of `Quiver.Path`, which is finite because the length
is pinned — but that finiteness may need to be supplied for `Nat.card` to behave. -/
theorem adjMatrix_pow_apply_eq_card_directedWalk
    {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (k : ℕ) (u v : V) :
    (D.adjMatrix ℕ ^ k) u v =
      Nat.card {p : @Quiver.Path V D.toQuiver u v // @Quiver.Path.length V D.toQuiver u v p = k} := by
  sorry

-- Ex 10.1.9: the condensation is acyclic.
/-- **Exercise 10.1.9** (B&M §10.1, verbatim).  *Show that the condensation `D̂` of
`D` contains no directed cycle.*

**Book proof.**  None — an exercise.

**Skeleton** (for `∀ c p, ¬ D.condensation.IsDirectedCycle p`).
1. `intro c p hcyc` and suppose the condensation has a directed cycle
   `c₀ → c₁ → … → c_n = c₀` through dicomponents.
2. **Lift each arc.**  By definition of `condensation`, each arc `cᵢ → c_{i+1}`
   comes with vertices `uᵢ ∈ cᵢ`, `vᵢ ∈ c_{i+1}` and `D.Adj uᵢ vᵢ`.
3. **Within a dicomponent, everything reaches everything.**  `vᵢ` and `u_{i+1}` lie
   in the same strongly connected component, so `D.Reachable vᵢ u_{i+1}`.  Chain
   these with the arcs of step 2 to get `D.Reachable u₀ u₀'` for representatives all
   the way round.
4. **Collapse.**  Going round the cycle both ways gives mutual reachability between
   representatives of `c₀` and `c₁`, so `c₀ = c₁` as strongly connected components.
5. That contradicts the `a ≠ b` clause of `condensation` — which is exactly why that
   clause is a *correction* to B&M's literal definition, and why it is load-bearing
   here rather than cosmetic.

**Reading.**  A directed cycle among dicomponents would merge them into one, so
contracting always produces an acyclic digraph — which by exercise 10.1.3(b) can be
topologically ordered.  §10.7 uses exactly this to rank the dicomponents of a
non-diconnected tournament in a dominance-preserving order, and exercise 10.2.1 uses
it on tournaments.

**Formalisation.**  Step 3 is where `Quiver.StronglyConnectedComponent`'s defining
property is consumed; the useful form is "same component ↔ mutually reachable",
which should be extracted first.  Note the statement quantifies over all base points
`c`, since `IsDirectedCycle` is stated for closed paths at a given vertex. -/
theorem condensation_acyclic {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) :
    ∀ (c : @Quiver.StronglyConnectedComponent V D.toQuiver)
      (p : @Quiver.Path _ D.condensation.toQuiver c c), ¬ D.condensation.IsDirectedCycle p := by
  sorry

open scoped Classical in
-- Ex 10.1.10: every graph has a balanced orientation `|d⁺ − d⁻| ≤ 1`.
-- NOTE: uses classical decidability of the existential `D.Adj` in place of the outline's
-- `∃ _ : DecidableRel D.Adj`, which does not register as an instance inside the body.
/-- **Exercise 10.1.10** (B&M §10.1, verbatim).  *Show that `G` has an orientation
`D` such that `|d⁺(v) - d⁻(v)| ≤ 1` for all `v ∈ V`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `∃ D, IsOrientationOf G ∧ ∀ v, |d⁺ - d⁻| ≤ 1`).
1. **Even out the degrees.**  Let `W` be the set of odd-degree vertices of `G`
   (even in number, by theorem 1.1).  Build `G⁺` on `V ⊕ Unit` by joining the new
   vertex to every member of `W`.  Then every degree of `G⁺` is even.
2. **Euler tour.**  `G⁺` has all degrees even, so by theorem 4.1 each of its
   components has an Euler tour.  (⚠ `G` need not be connected, so work
   component-by-component; the book glosses over this.)
3. **Orient along the tour.**  Direct each edge the way the tour traverses it.
4. **Balance at old vertices.**  Each visit of the tour to a vertex uses one arc in
   and one out, so in `G⁺` every vertex has `d⁺ = d⁻` exactly.
5. **Delete the new vertex.**  Removing it removes at most one incident arc at each
   `v ∈ W` — one *in* or one *out* — so `|d⁺(v) - d⁻(v)| ≤ 1` there and `= 0`
   elsewhere.  This is exactly where the slack of one comes from.
6. Check the result is an `IsOrientationOf G`: the underlying graph is `G` and no
   edge became two-way.

**Reading.**  Every graph can be made one-way in a *balanced* way, with the traffic
into and out of each junction differing by at most one.  Contrast exercise 10.6.1,
which shows the stronger set-wise balance — `||(S, S̄)| - |(S̄, S)|| ≤ 1` for every
vertex *set* `S` — is **not** always achievable, the Petersen graph being a
counterexample.

**Formalisation.**  The conclusion is stated as two `ℤ` inequalities rather than
`|·| ≤ 1`, avoiding `Int.natAbs` juggling.  The `open scoped Classical in` supplies
decidability of the existentially-bound `D.Adj`; the outline's
`∃ _ : DecidableRel D.Adj` does not register as an instance inside the body, which
is why it was replaced. -/
theorem exists_balanced_orientation
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ D : Digraph V, D.IsOrientationOf G ∧
      ∀ v : V, (D.outdegree v : ℤ) - (D.indegree v : ℤ) ≤ 1 ∧
               (D.indegree v : ℤ) - (D.outdegree v : ℤ) ≤ 1 := by
  sorry

/-! ## §10.2 -/

-- Thm 10.1 (Roy–Gallai): a digraph contains a directed path of length `χ − 1`.
/-- **Theorem 10.1** (Roy, 1967; Gallai, 1968).  *A digraph `D` contains a directed
path of length `χ - 1`*, where `χ` is the chromatic number of the underlying
graph.

**Book proof** (B&M §10.2, verbatim).  *Let `A'` be a minimal set of arcs of `D` such
that `D' = D - A'` contains no directed cycle, and let the length of a longest
directed path in `D'` be `k`.  Now assign colours `1, 2, …, k+1` to the vertices of
`D'` by assigning colour `i` to vertex `v` if the length of a longest directed path
in `D'` with origin `v` is `i - 1`.  Denote by `Vᵢ` the set of vertices with colour
`i`.  We shall show that `(V₁, V₂, …, V_{k+1})` is a proper `(k+1)`-vertex colouring
of `D`.*

*First, observe that the origin and terminus of any directed path in `D'` have
different colours.  For let `P` be a directed `(u, v)`-path of positive length in
`D'` and suppose `v ∈ Vᵢ`.  Then there is a directed path `Q = (v₁, v₂, …, vᵢ)` in
`D'`, where `v₁ = v`.  Since `D'` contains no directed cycle, `PQ` is a directed
path with origin `u` and length at least `i`.  Thus `u ∉ Vᵢ`.*

*We can now show that the ends of any arc of `D` have different colours.  Suppose
`(u, v) ∈ A(D)`.  If `(u, v) ∈ A(D')` then `(u, v)` is a directed path in `D'` and
so `u` and `v` have different colours.  Otherwise, `(u, v) ∈ A'`.  By the minimality
of `A'`, `D' + (u, v)` contains a directed cycle `C`.  `C - (u, v)` is a directed
`(v, u)`-path in `D'` and hence in this case, too, `u` and `v` have different
colours.*

*Thus `(V₁, V₂, …, V_{k+1})` is a proper vertex colouring of `D`.  It follows that
`χ ≤ k + 1`, and so `D` has a directed path of length `k ≥ χ - 1`.*

**Skeleton** (for `∃ u v p, IsDirectedPath p ∧ k - 1 ≤ p.length`, `k = χ`).
1. **Choose `A'` minimal.**  The set of arc-sets whose removal kills all directed
   cycles is nonempty (remove everything) and finite, so pick a minimal member.
   Define `D'` as `D` with those arcs deleted; record `hacyc : D'` acyclic and
   `hmin`: adding back any arc of `A'` creates a directed cycle.
2. **`k' :=` longest directed path length in `D'`.**  Attained, as in exercise
   10.1.6 step 1.
3. **The colouring.**  `c v :=` the length of a longest directed path in `D'` with
   origin `v`.  Values lie in `Fin (k' + 1)`.
4. **Key lemma (`c` strictly decreases along `D'`-paths).**  If there is a
   `D'`-path of positive length from `u` to `v` then `c u > c v` — concatenate a
   longest path out of `v`, using acyclicity to know the concatenation is still a
   *path*.  In particular `c u ≠ c v`.
5. **`c` is proper for `D`'s underlying graph.**  Take an arc `(u,v)` of `D`.  Either
   it survives in `D'` (step 4 with the one-arc path), or it lies in `A'` and `hmin`
   gives a directed cycle in `D' + (u,v)`, whose remainder is a `D'`-path from `v`
   to `u` — step 4 again, the other way round.
6. Hence `χ ≤ k' + 1`, so `k ≤ k' + 1`, i.e. `k - 1 ≤ k'`; instantiate the goal with
   the longest path of step 2.

**Reading.**  Striking because, as figure 10.3 shows, there is otherwise *no close
relationship between the lengths of paths and directed paths in a digraph* — yet the
chromatic number of the underlying graph controls the latter exactly.  The remark
following shows the bound is best possible.

**Formalisation.**  `k - 1` is ℕ-subtraction, harmless as the goal is a lower bound.
`hk` pins `χ` of `toSimpleGraphInclusive` — the underlying graph — to `k` in `ℕ∞`.
Step 4 is the mathematical core; steps 1 and 2 are both "choose a maximum/minimum in
a finite nonempty family" and should share a helper. -/
theorem roy_gallai_directed_path
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    {k : ℕ} (hk : D.toSimpleGraphInclusive.chromaticNumber = (k : ℕ∞)) :
    ∃ (u v : V) (p : @Quiver.Path V D.toQuiver u v),
      D.IsDirectedPath p ∧ k - 1 ≤ @Quiver.Path.length V D.toQuiver u v p := by
  sorry

-- (10.1′): Thm 10.1 is best possible — an orientation whose longest directed path is `χ − 1`.
/-- **Book remark following theorem 10.1** (B&M §10.2, verbatim).  *Theorem 10.1 is
best possible in that every graph `G` has an orientation in which the longest
directed path is of length `χ - 1`.  Given a proper `χ`-vertex colouring
`(V₁, V₂, …, V_χ)` of `G`, we orient `G` by converting edge `uv` to arc `(u, v)` if
`u ∈ Vᵢ` and `v ∈ Vⱼ` with `i < j`.  Clearly, no directed path in this orientation
of `G` can contain more than `χ` vertices, since no two vertices of the path can
have the same colour.*

**Book proof.**  The passage above *is* the proof; B&M give it inline rather than as
a displayed argument.

**Skeleton** (for `∃ D, IsOrientationOf G ∧ ∀ p, IsDirectedPath p → p.length ≤ k - 1`,
given `hcol : G.Colorable k`).
1. **Get the colouring.**  `hcol` yields `c : G.Coloring (Fin k)`.
2. **Define the orientation.**  `D.Adj u v := G.Adj u v ∧ c u < c v`.
3. **It is an orientation.**  Underlying graph: for an edge `uv`, properness gives
   `c u ≠ c v`, so exactly one of `c u < c v`, `c v < c u` holds — hence
   `toSimpleGraphInclusive D = G`, and the second clause of `IsOrientationOf`
   (never both directions) is immediate from `<` being asymmetric.
4. **Colours strictly increase along directed paths.**  Induct on the path: each arc
   raises `c`.  So the map `vertex ↦ c vertex` is *injective* on a directed path.
5. **Length bound.**  A directed path's vertices are therefore distinct colours in
   `Fin k`, so it has at most `k` vertices and length at most `k - 1`.

**Reading.**  Orient every edge from the lower colour class to the higher.  Along a
directed path the colour index strictly increases, so the path has at most `χ`
vertices.  Combined with theorem 10.1 this shows `χ - 1` is exactly the right
bound.  Note the orientation is automatically acyclic, the colour index being a
topological ordering — so this also witnesses exercise 10.1.3(b) in reverse.

**Formalisation.**  Stated with an arbitrary `k`-colouring rather than an optimal
one, which is the usable form: exercise 10.2.6(a) instantiates it at `k = Δ + 1`
via corollary 8.1.2, not at `k = χ`.  Step 4's injectivity is a cleaner invariant
to carry than the book's "no two vertices share a colour". -/
theorem exists_orientation_longest_directedPath_le
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hcol : G.Colorable k) :
    ∃ D : Digraph V, D.IsOrientationOf G ∧
      ∀ (u v : V) (p : @Quiver.Path V D.toQuiver u v), D.IsDirectedPath p →
        @Quiver.Path.length V D.toQuiver u v p ≤ k - 1 := by
  sorry

-- Cor 10.1 (Rédei): every tournament has a directed Hamilton path.
/-- **Corollary 10.1** (Rédei, 1934).  *Every tournament has a directed Hamilton
path.*

B&M define the term just above: *A directed Hamilton path of `D` is a directed path
that includes every vertex of `D`.*

**Book proof** (B&M §10.2, verbatim).  *If `D` is a tournament, then `χ = ν`.*

**Skeleton** (for `∃ u v p, IsDirectedPath p ∧ ∀ w, w ∈ p.vertices`).  The book's
one-liner unpacks into three steps.
1. **`χ = ν` for a tournament.**  Its underlying graph is complete (every two
   distinct vertices are joined, by `IsTournament`'s second clause), and
   `χ(K_ν) = ν`.  Both halves need proving: `toSimpleGraphInclusive D = ⊤`, then
   Mathlib's chromatic number of a complete graph.
2. **Apply theorem 10.1** at `k = ν`, obtaining a directed path of length
   `≥ ν - 1`.
3. **Length `ν - 1` forces spanning.**  A directed path has `Nodup` vertices, so
   `length + 1 = |vertices| ≤ ν`; with `length ≥ ν - 1` the vertex list has exactly
   `ν` distinct entries and therefore contains every vertex.  This is the step that
   turns theorem 10.1's *length* bound into the goal's *spanning* claim.

**Reading.**  In any round-robin competition the players can be lined up so that
each beat the next.  The book cautions in §10.7 that this does *not* give a sensible
ranking, since a tournament generally has many directed Hamilton paths — the
six-player example has `(3,1,2,4,5,6)`, `(1,2,4,5,6,3)`, `(1,4,6,3,2,5)` and others,
declaring different winners.  That is what motivates the eigenvector method.

**Formalisation.**  "Includes every vertex" is `∀ w, w ∈ p.vertices` rather than a
cardinality claim, which is what step 3 delivers most directly.  Exercise 10.2.3
gives an independent route not passing through theorem 10.1. -/
theorem redei_directed_hamilton_path
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (htour : D.IsTournament) :
    ∃ (u v : V) (p : @Quiver.Path V D.toQuiver u v),
      D.IsDirectedPath p ∧ ∀ w : V, w ∈ (@Quiver.Path.vertices V D.toQuiver u v p) := by
  sorry

-- Thm 10.2 (Chvátal–Lovász): every loopless digraph has a semi-kernel.
/-- **Theorem 10.2** (Chvátal and Lovász, 1974).  *A loopless digraph `D` has an
independent set `S` such that each vertex of `D` not in `S` is reachable from a
vertex in `S` by a directed path of length at most two.*

**Book proof** (B&M §10.2, verbatim).  *By induction on `ν`.  The theorem holds
trivially for `ν = 1`.  Assume that it is true for all digraphs with fewer than `ν`
vertices, and let `v` be an arbitrary vertex of `D`.  By the induction hypothesis
there exists in `D' = D - ({v} ∪ N⁺(v))` an independent set `S'` such that each
vertex of `D'` not in `S'` is reachable from a vertex in `S'` by a directed path of
length at most two.  If `v` is an out-neighbour of some vertex `u` of `S'`, then
every vertex of `N⁺(v)` is reachable from `u` by a directed path of length two.
Hence, in this case, `S = S'` satisfies the required property.  If, on the other
hand, `v` is not an out-neighbour of any vertex of `S'`, then `v` is joined to no
vertex of `S'` and the independent set `S = S' ∪ {v}` has the required property.*

**Skeleton** (for `∃ S, IsIndepSet S ∧ ∀ v ∉ S, ∃ u ∈ S, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v`).
1. **Strong induction on `card V`**, generalising the carrier — the recursive call is
   about `D.induce ({v} ∪ N⁺(v))ᶜ`, a strictly smaller vertex set (it loses at least
   `v`).
2. **Base.**  `card V ≤ 1`: take `S = univ`, independence is vacuous and the second
   clause has no `v ∉ S`.
3. **Step.**  Pick any `v`.  Apply the induction hypothesis to
   `D' = D.induce ({v} ∪ N⁺(v))ᶜ`, giving `S'`.
4. **Case A: `v` is an out-neighbour of some `u ∈ S'`.**  Take `S = S'`.  The vertices
   to check are those outside `S'`: those in `D'` are handled by the induction
   hypothesis; `v` itself by the arc `u → v`; and each `w ∈ N⁺(v)` by the two-step
   path `u → v → w`.
5. **Case B: `v` is an out-neighbour of nothing in `S'`.**  Take `S = S' ∪ {v}`.
   Independence: no arc runs from `S'` to `v` by the case assumption, and none from
   `v` to `S'` since `N⁺(v)` was deleted.  ⚠ Independence is in the *underlying
   graph*, so **both** directions must be excluded — the book says "`v` is joined to
   no vertex of `S'`", quietly using both facts.  Coverage: `N⁺(v)` is reached from
   `v` in one step, the rest by the induction hypothesis.

**Reading.**  Such a set is called a **semi-kernel**.  The independence requirement
is what makes it non-trivial — one wants mutually non-adjacent "dominators" from
which everything else is within two steps.  Corollary 10.2 is the tournament case,
where independence forces `|S| = 1`.

**Formalisation.**  The `u = v` disjunct in the goal covers the reflexive case and is
not in the book, which says "each vertex *not in* `S`"; it is harmless and makes the
statement easier to instantiate.  `hloop : Irreflexive D.Adj` is B&M's "loopless".
`IsIndepSet` is taken in `toSimpleGraphInclusive`, matching "independent set" for the
underlying graph. -/
theorem chvatal_lovasz_semikernel
    {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (hloop : Irreflexive D.Adj) :
    ∃ S : Set V, D.toSimpleGraphInclusive.IsIndepSet S ∧
      ∀ v ∉ S, ∃ u ∈ S, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v := by
  sorry

-- Cor 10.2: a tournament has a vertex reaching every other in `≤ 2` steps.
/-- **Corollary 10.2.**  *A tournament contains a vertex from which every other
vertex is reachable by a directed path of length at most two.*

**Book proof** (B&M §10.2, verbatim).  *If `D` is a tournament, then `α = 1`.*

**Skeleton** (for `∃ u, ∀ v ≠ u, D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v`).
1. **A tournament is loopless.**  `IsTournament`'s first clause is `Irreflexive`,
   feeding theorem 10.2's hypothesis.
2. **Apply theorem 10.2** to get a semi-kernel `S`.
3. **`S` is a singleton.**  Every two distinct vertices of a tournament are adjacent
   in the underlying graph, so an independent set has at most one element; and `S`
   is nonempty, since otherwise the second clause of theorem 10.2 would be
   unsatisfiable for any `v` (with `[Nonempty V]` supplying such a `v`).  ⚠ Both
   halves need proof — the book's "`α = 1`" asserts them together.
4. Let `u` be its unique element and read off the conclusion from theorem 10.2's
   second clause, discarding the `u = v` disjunct via `v ≠ u`.

**Reading.**  Such a vertex is called a **king**: a player who, for every other
player `v`, either beat `v` directly or beat someone who beat `v`.  Exercise 10.2.4
gives a direct proof — take a vertex of maximum outdegree — which is dropped from
this file as a second proof of the same statement.  Note a king need not have won
the most games, and a tournament may have several kings.

**Formalisation.**  `[Nonempty V]` is load-bearing for step 3; without it `S = ∅` is
a legitimate semi-kernel and no `u` exists. -/
theorem tournament_exists_king
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (htour : D.IsTournament) :
    ∃ u : V, ∀ v : V, v ≠ u → (D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) := by
  sorry

-- Ex 10.2.1: a tournament is diconnected, or becomes so after reorienting one arc.
/-- **Exercise 10.2.1** (B&M §10.2, verbatim).  *Show that every tournament is either
diconnected or can be transformed into a diconnected tournament by the
reorientation of just one arc.*

**Book proof.**  None — an exercise.

**Skeleton** (for `D.Diconnected ∨ ∃ x y, D.Adj x y ∧ (reorient x y D).Diconnected`).
1. `by_cases` on `D.Diconnected`; the left disjunct is immediate.
2. **The dicomponents are totally ordered.**  The condensation is acyclic (exercise
   10.1.9) and — because every two vertices of a tournament are adjacent — every two
   *distinct* dicomponents have an arc between them.  An acyclic digraph in which
   every pair is joined is a transitive tournament, hence linearly ordered: use
   `exists_topological_ordering` on the condensation and note the order is total.
3. **Dominance is wholesale.**  If `Dᵢ` precedes `Dⱼ` then *every* vertex of `Dᵢ`
   beats *every* vertex of `Dⱼ` — otherwise an arc back would put them in one
   dicomponent.  Establish this as a `have`; it is what makes step 4's single
   reversal enough.
4. **Reverse one arc from first to last.**  Take `x` in the first dicomponent, `y` in
   the last; `D.Adj x y` by step 3.  Reversing it makes `y` reach `x`, and combined
   with the chain `x ⇝ … ⇝ y` through the ordered dicomponents, every vertex now
   reaches every other.
5. Check the reoriented digraph is still a tournament and is diconnected.

**Reading.**  Tournaments are never far from diconnected: a single reversed result
suffices to make every player reachable from every other.  Step 3 is the tournament
speciality — in a general digraph the dicomponents form only a partial order, and
one reversal would not do.

**Formalisation.**  The reorientation is written inline as an `if`-cascade on `Adj`
rather than via a helper: `(x,y)` is removed, `(y,x)` added, everything else kept.
Note the `if (u = y ∧ v = x) then True` branch must come *after* the `(x,y)` branch,
which it does. -/
theorem tournament_diconnected_or_reorient_one
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (htour : D.IsTournament) :
    D.Diconnected ∨ ∃ x y : V, D.Adj x y ∧
      (Digraph.mk fun u v => if (u = x ∧ v = y) then False
                             else if (u = y ∧ v = x) then True else D.Adj u v).Diconnected := by
  sorry

-- Ex 10.2.2*: unilateral ⇔ has a spanning directed walk (B&M genuinely means *walk*).
/-- **Exercise 10.2.2***.  *`D` is unilateral if and only if `D` has a spanning
directed walk.*

**Book proof.**  None — an exercise, and one the book **stars**.

**Skeleton** (for `IsUnilateral ↔ ∃ u v p, ∀ w, w ∈ p.vertices`).

*(⇐) a spanning walk gives unilaterality.*
1. Given a walk `p` through every vertex and any `u`, `v`: both occur in
   `p.vertices`.  Whichever occurs first reaches the other along the corresponding
   section of `p`, so `Reachable u v ∨ Reachable v u`.
2. The one real step is extracting a sub-walk between two positions of a
   `Quiver.Path` and reading off `ReflTransGen` from it.

*(⇒) unilaterality gives a spanning walk.*
3. **Reachability is a total preorder.**  It is reflexive and transitive
   (`ReflTransGen`), and `IsUnilateral` makes it total.
4. **Order the vertices.**  Pick a linear order `v₁, …, v_ν` refining it, so that
   `Reachable vᵢ v_{i+1}` for each `i`.  ⚠ This needs care: totality plus
   transitivity gives a total preorder, and a linearisation must be *chosen* — the
   quotient by mutual reachability is a total order (the condensation of exercise
   10.1.9, now linear), so topologically order that and lift.
5. **Concatenate.**  Splice directed walks `v₁ ⇝ v₂ ⇝ … ⇝ v_ν` into a single walk;
   it meets every vertex by construction.

**Reading.**  Unilateral means any two vertices are comparable — you can get from
one to the other, though perhaps only one way round.  It sits strictly between
"connected" and "diconnected".

**Formalisation.**  ⚠ The book genuinely means *walk*, not path: revisiting vertices
is essential, since a spanning directed **path** would be a Hamilton path and is a
far stronger requirement.  The Lean statement accordingly asks only for a
`Quiver.Path` (= directed walk) whose `vertices` cover `V`, with **no** `Nodup`
condition — do not be tempted to add `IsDirectedPath`. -/
theorem isUnilateral_iff_exists_spanning_directedWalk
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj] :
    D.IsUnilateral ↔
      ∃ (u v : V) (p : @Quiver.Path V D.toQuiver u v),
        ∀ w : V, w ∈ (@Quiver.Path.vertices V D.toQuiver u v p) := by
  sorry

-- Ex 10.2.3(a): a non-Hamilton maximal directed path in a tournament can absorb an outside vertex.
/-- **Exercise 10.2.3(a).**  *Let `P = (v₁, …, v_k)` be a maximal directed path in a
tournament `D`.  Suppose `P` is not a directed Hamilton path and let `v` be any
vertex not on `P`.  Then for some `i`, both `(vᵢ, v)` and `(v, v_{i+1})` are arcs
of `D`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `∃ i, ∃ h : i + 1 < l.length, D.Adj l[i] v ∧ D.Adj v l[i+1]`).
1. **Every vertex of `P` is comparable with `v`.**  `htour` plus `hv : v ∉ l` gives,
   for each `w ∈ l`, exactly one of `D.Adj w v`, `D.Adj v w`.
2. **Maximality pins the two ends.**  `hmax` says no outside vertex has an arc *to*
   `l.head!` or *from* `l.getLast!`.  Applied to `v`: `¬ D.Adj v l.head!`, so by
   step 1 `D.Adj l.head! v`; and `¬ D.Adj l.getLast! v`, so `D.Adj v l.getLast!`.
3. **A switch must occur.**  Consider the boolean sequence `i ↦ (D.Adj l[i] v)`
   along the list.  It is `true` at `i = 0` and `false` at the last index (step 2,
   using step 1 to convert). So there is a least `i` with `D.Adj l[i] v` true and
   `D.Adj l[i+1] v` false; step 1 turns the latter into `D.Adj v l[i+1]`.
   Formally: induct along the list, or use `List.exists_of_...` on the first index
   where the predicate flips.
4. Produce `i` together with its bound `i + 1 < l.length`.

**Reading.**  Because `D` is a tournament, `v` is joined to every vertex of `P` in
one direction or the other; maximality forces `v₁ → v` at the start and
`v → v_k` at the end, so travelling along `P` the direction must switch somewhere.
Part (b) — dropped here, being a re-derivation of corollary 10.1 — inserts `v` at
that point to get a longer directed path and repeats until it spans.

**Formalisation.**  The path is presented as a `List V` with `IsChain D.Adj` rather
than as a `Quiver.Path`, since the statement indexes into it (`l[i]`, `l[i+1]`) and
lists index far more comfortably.  `[Inhabited V]` supports `head!`/`getLast!` in
`hmax`; `hne : l ≠ []` keeps those meaningful. -/
theorem tournament_maximal_directedPath_insert
    {V : Type*} [Fintype V] [Inhabited V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (htour : D.IsTournament) (l : List V) (hne : l ≠ []) (hnd : l.Nodup)
    (hchain : l.IsChain D.Adj)
    (hmax : ∀ w ∉ l, ¬ D.Adj w l.head! ∧ ¬ D.Adj l.getLast! w)
    {v : V} (hv : v ∉ l) :
    ∃ i, ∃ h : i + 1 < l.length, D.Adj l[i] v ∧ D.Adj v l[i+1] := by
  sorry

-- DROPPED: Ex 10.2.3(b) — "Deduce Rédei's theorem": a re-derivation of Cor 10.1, not a new statement.

-- DROPPED: Ex 10.2.4 — "Prove corollary 10.2 by considering…": alternative proof of Cor 10.2.

-- Ex 10.2.5(a)*: Chvátal–Komlós — a monotone directed path when `χ > mn`.
/-- **Exercise 10.2.5(a)*** (Chvátal and Komlós).  *Let `D` be a digraph with
`χ > mn`, and let `f` be a real-valued function on `V`.  Then `D` has either a
directed path `(u₀, …, u_m)` with `f(u₀) ≤ f(u₁) ≤ … ≤ f(u_m)`, or a directed path
`(v₀, …, v_n)` with `f(v₀) > f(v₁) > … > f(v_n)`.*

**Book proof.**  None — an exercise, and one the book **stars**.

**Skeleton** (for the disjunction of a weakly-increasing chain of length `m + 1` and
a strictly-decreasing one of length `n + 1`).
1. `by_contra`: assume neither exists.
2. **The pair colouring.**  For each vertex `w` let
   `a w :=` the length of a longest `f`-weakly-increasing directed path *ending* at
   `w`, and `b w :=` the length of a longest `f`-strictly-decreasing one ending at
   `w`.  By assumption `a w < m` and `b w < n`, so `(a, b) : V → Fin m × Fin n`.
3. **It is a proper colouring.**  For an arc `(u, w)` of `D`, compare `f u` and
   `f w`: if `f u ≤ f w` then any weakly-increasing path ending at `u` extends
   through the arc, so `a w > a u`; otherwise `f u > f w` and likewise `b w > b u`.
   Either way `(a u, b u) ≠ (a w, b w)`.
4. Hence `χ ≤ m * n`, contradicting `hchi`.

**Reading.**  Theorem 10.1 says a high chromatic number forces a long directed path;
this refines it by controlling how `f` behaves along that path.  A large enough
chromatic number forces a *monotone* directed path — weakly increasing of length
`m`, or strictly decreasing of length `n`.  Part (b) reads off Erdős–Szekeres.

**Formalisation.**  Paths are `List V` with two `IsChain`s — one for adjacency, one
for the `f`-comparison — plus `Nodup`, rather than `Quiver.Path`s, so that the
monotonicity condition can be stated alongside.  Note the asymmetry `≤` versus `>`
is the book's and is essential: with two weak orders step 3 would fail on an arc
where `f u = f w`. -/
theorem chvatal_komlos_monotone_directedPath
    {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (f : V → ℝ) {m n : ℕ}
    (hchi : (m * n : ℕ∞) < D.toSimpleGraphInclusive.chromaticNumber) :
    (∃ l : List V, l.length = m + 1 ∧ l.IsChain D.Adj ∧ l.Nodup ∧ l.IsChain (f · ≤ f ·)) ∨
    (∃ l : List V, l.length = n + 1 ∧ l.IsChain D.Adj ∧ l.Nodup ∧ l.IsChain (f · > f ·)) := by
  sorry

-- Ex 10.2.5(b)*: Erdős–Szekeres (RESTATED; `Archive` version is NOT importable, derive from (a)).
/-- **Exercise 10.2.5(b)*** (Erdős and Szekeres).  *Deduce that any sequence of
`mn + 1` distinct integers contains either an increasing subsequence of `m` terms
or a decreasing subsequence of `n` terms.*

**Book proof.**  None — an exercise; "deduce" points at part (a).

**Skeleton** (for the disjunction of an increasing and a decreasing `Finset (Fin N)`).
1. **Build the transitive tournament** `T` on `Fin N`: `T.Adj i j := i < j`.  Its
   underlying graph is complete, so `χ = N > m * n` by `hN` — supplying part (a)'s
   hypothesis.
2. **Apply part (a)** with `f := fun i => (g i : ℝ)`, obtaining either a weakly
   increasing directed path of length `m` or a strictly decreasing one of length
   `n`.
3. **Translate paths to subsequences.**  A directed path in `T` is a strictly
   increasing list of *indices*; its vertex list, taken as a `Finset`, has the
   required cardinality (`Nodup`), and the chain condition on `f` becomes the
   monotonicity of `g` along it.
4. **Upgrade weak to strict.**  Part (a)'s first alternative is only `f ≤ f`; the
   goal wants `g i < g j`.  `hinj` closes the gap: distinct positions have distinct
   values, so `≤` plus `≠` gives `<`.  ⚠ This is where `Function.Injective g` is
   spent — the book's "distinct integers".
5. Note the goal's ordering condition is `∀ i ∈ s, ∀ j ∈ s, i < j → …`, so a
   `Finset` suffices and the list order need not be retained.

**Reading.**  The classical Erdős–Szekeres theorem, obtained as a special case of a
statement about digraphs — a good illustration of the chapter's theme that
chromatic number controls directed-path structure.

**Formalisation.**  ⚠ Restated: Mathlib's `Archive` version is not importable, so
the statement is spelled out here and derived from (a) as the book intends.  `g` is
`ℤ`-valued (the book's "integers") while part (a) needs `ℝ`, hence the cast in step
2.  `hN : m * n < N` is the book's "`mn + 1` terms", generalised to any longer
sequence. -/
theorem erdos_szekeres_of_chvatal_komlos
    {m n : ℕ} {N : ℕ} (hN : m * n < N) (g : Fin N → ℤ) (hinj : Function.Injective g) :
    (∃ s : Finset (Fin N), s.card = m ∧ ∀ i ∈ s, ∀ j ∈ s, i < j → g i < g j) ∨
    (∃ s : Finset (Fin N), s.card = n ∧ ∀ i ∈ s, ∀ j ∈ s, i < j → g j < g i) := by
  sorry

-- Ex 10.2.6(a): an orientation whose directed paths have length `≤ Δ`.
-- NOTE: rides ch8's cor 8.1.2 (`χ ≤ Δ+1`), which is out of chapter; kept via the shared layer.
/-- **Exercise 10.2.6(a).**  *Using theorem 10.1 and corollary 8.1.2, show that `G`
has an orientation in which each directed path is of length at most `Δ`.*

**Book proof.**  None — an exercise, but both ingredients are named.

**Skeleton** (for `∃ D, IsOrientationOf G ∧ ∀ p, IsDirectedPath p → p.length ≤ G.maxDegree`).
1. **Corollary 8.1.2** gives `G.Colorable (G.maxDegree + 1)` — every graph satisfies
   `χ ≤ Δ + 1`.
2. **Apply `exists_orientation_longest_directedPath_le`** (the remark after theorem
   10.1) at `k = G.maxDegree + 1`, obtaining an orientation whose directed paths have
   length at most `k - 1`.
3. `(G.maxDegree + 1) - 1 = G.maxDegree` in `ℕ` — no truncation, the `+1` guarantees
   it.  Rewrite and conclude.

**Reading.**  Chaining two results already available: `χ ≤ Δ + 1` bounds the palette,
and the colour-increasing orientation turns a palette bound into a path bound.  Part
(b) of the exercise — dropped here, being the same statement — asks for a
constructive proof avoiding the chromatic detour.

**Formalisation.**  ⚠ This rides chapter 8's corollary 8.1.2, which is out of
chapter; step 1 is therefore an import from
`TCSlib/GraphTheory/VertexColourings.lean` (`chromaticNumber_le_maxDegree_add_one`)
rather than something proved here.  Note the shape of step 2: this is exactly why
the theorem-10.1 remark was stated for an arbitrary `k`-colouring rather than an
optimal one. -/
theorem exists_orientation_directedPath_le_maxDegree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ D : Digraph V, D.IsOrientationOf G ∧
      ∀ (u v : V) (p : @Quiver.Path V D.toQuiver u v), D.IsDirectedPath p →
        @Quiver.Path.length V D.toQuiver u v p ≤ G.maxDegree := by
  sorry

-- DROPPED: Ex 10.2.6(b) — "Give a constructive proof of (a)": same statement as 10.2.6(a).

/-! ## §10.3 -/

-- Thm 10.3 (Moon): a diconnected tournament with `ν ≥ 3` is vertex-pancyclic.
/-- **Theorem 10.3** (Moon, 1966).  *Each vertex of a diconnected tournament `D`
with `ν ≥ 3` is contained in a directed `k`-cycle, `3 ≤ k ≤ ν`.*

**Book proof** (B&M §10.3, verbatim).  *Let `D` be a diconnected tournament with
`ν ≥ 3`, and let `u` be any vertex of `D`.  Set `S = N⁺(u)` and `T = N⁻(u)`.  We
first show that `u` is in a directed 3-cycle.  Since `D` is diconnected, neither `S`
nor `T` can be empty; and, for the same reason, `(S, T)` must be nonempty (see
figure 10.5).  There is thus some arc `(v, w)` in `D` with `v ∈ S` and `w ∈ T`, and
`u` is in the directed 3-cycle `(u, v, w, u)`.*

*The theorem is now proved by induction on `k`.  Suppose that `u` is in directed
cycles of all lengths between 3 and `n`, where `n < ν`.  We shall show that `u` is
in a directed `(n+1)`-cycle.*

*Let `C = (v₀, v₁, …, v_n)` be a directed `n`-cycle in which `v₀ = v_n = u`.  If
there is a vertex `v` in `V(D) \ V(C)` which is both the head of an arc with tail in
`C` and the tail of an arc with head in `C`, then there are adjacent vertices `vᵢ`
and `v_{i+1}` on `C` such that both `(vᵢ, v)` and `(v, v_{i+1})` are arcs of `D`.
In this case `u` is in the directed `(n+1)`-cycle `(v₀, v₁, …, vᵢ, v, v_{i+1}, …, v_n)`.*

*Otherwise, denote by `S` the set of vertices in `V(D) \ V(C)` which are heads of
arcs joined to `C`, and by `T` the set of vertices in `V(D) \ V(C)` which are tails
of arcs joined to `C` (see figure 10.6).*

*As before, since `D` is diconnected, `S`, `T` and `(S, T)` are all nonempty, and
there is some arc `(v, w)` in `D` with `v ∈ S` and `w ∈ T`.  Hence `u` is in the
directed `(n+1)`-cycle `(v₀, v, w, v₂, …, v_n)`.*

**Skeleton** (for `∃ p : Path u u, IsDirectedCycle p ∧ p.length = k`, `3 ≤ k ≤ ν`).
1. **Reusable lemma: `(S, T)` is nonempty.**  For a diconnected `D` and a partition
   with `S`, `T` nonempty and no arc `S → T`, reachability from `S` to `T` fails.
   Both the base case and the induction step invoke this; prove it once.
2. **Base `k = 3`.**  `S = N⁺(u)`, `T = N⁻(u)`.  Both nonempty by diconnection
   (`u` must reach something and be reached).  Step 1 gives an arc `v → w` with
   `v ∈ S`, `w ∈ T`, and `u → v → w → u` is the 3-cycle.
3. **Induction on `k` from `3` to `ν`.**  Given an `n`-cycle `C` through `u` with
   `n < ν`, produce an `(n+1)`-cycle.
4. **Case A — some off-cycle `v` has an arc from `C` and an arc to `C`.**  Walking
   round `C`, the predicate "`vᵢ → v`" holds somewhere and fails somewhere, so it
   flips at some `i`: `(vᵢ, v)` and `(v, v_{i+1})` are both arcs (using
   tournament-completeness to convert the failure into the reverse arc).  Insert `v`.
   *This is the same "direction must switch" argument as exercise 10.2.3(a)* — share
   it.
5. **Case B — no such `v`.**  Split the off-cycle vertices into `S` (heads of arcs
   from `C`) and `T` (tails of arcs to `C`); case A's failure makes these disjoint
   and, with tournament-completeness, exhaustive.  Step 1 supplies `v → w` with
   `v ∈ S`, `w ∈ T`, and the book's splice gives the `(n+1)`-cycle.

**Reading.**  A digraph with this property is **vertex-pancyclic**: every vertex lies
on cycles of *every* possible length.  Taking `k = ν`, every diconnected tournament
has a directed Hamilton cycle — first proved by Camion (1959).  Theorem 10.7
consumes the full strength, needing cycles of several specific lengths through a
given vertex.

**Formalisation.**  The cycle is based at `u` (`p : Path u u`), which is how "`u` is
contained in" is expressed.  ⚠ The book's final splice `(v₀, v, w, v₂, …, v_n)`
silently assumes `v` follows `v₀` and `w` precedes `v₂`; check the index bookkeeping
against `n ≥ 3` before trusting it. -/
theorem moon_vertex_pancyclic
    {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (htour : D.IsTournament) (hdicon : D.Diconnected) (hv : 3 ≤ Fintype.card V)
    (u : V) {k : ℕ} (hk3 : 3 ≤ k) (hkv : k ≤ Fintype.card V) :
    ∃ p : @Quiver.Path V D.toQuiver u u,
      D.IsDirectedCycle p ∧ @Quiver.Path.length V D.toQuiver u u p = k := by
  sorry

-- Thm 10.4 (Ghouila-Houri): strict with `ν ≤ 2·min{d⁻,d⁺}` and `ν > 2` ⇒ a directed Hamilton cycle.
/-- **Theorem 10.4** (a special case of Ghouila-Houri, 1960).  *If `D` is strict and
`min{δ⁻, δ⁺} ≥ ν/2 > 1`, then `D` contains a directed Hamilton cycle.*

**Book proof** (B&M §10.3, verbatim).  *Suppose that `D` satisfies the hypotheses of
the theorem, but does not contain a directed Hamilton cycle.  Denote the length of a
longest directed cycle in `D` by `l`, and let `C = (v₁, v₂, …, v_l, v₁)` be a
directed cycle in `D` of length `l`.  We note that `l > ν/2` (exercise 10.1.7).  Let
`P` be a longest directed path in `D - V(C)` and suppose that `P` has origin `u`,
terminus `v` and length `m` (see figure 10.7).  Clearly*

    ν ≥ l + m + 1                                                    (10.1)

*and, since `l > ν/2`,*

    m < ν/2                                                          (10.2)

*Set `S = {i | (v_{i-1}, u) ∈ A}` and `T = {i | (v, vᵢ) ∈ A}`.*

*We first show that `S` and `T` are disjoint.  Let `C_{j,k}` denote the section of
`C` with origin `vⱼ` and terminus `v_k`.  If some integer `i` were in both `S` and
`T`, `D` would contain the directed cycle `C_{i,i-1}(v_{i-1}, u)P(v, vᵢ)` of length
`l + m + 1`, contradicting the choice of `C`.  Thus*

    S ∩ T = ∅                                                        (10.3)

*Now, because `P` is a maximal directed path in `D - V(C)`,
`N⁻(u) ⊆ V(P) ∪ V(C)`.  But the number of in-neighbours of `u` in `C` is precisely
`|S|` and so `d⁻_D(u) = d⁻_P(u) + |S|`.  Since `d⁻_D(u) ≥ δ⁻ ≥ ν/2` and
`d⁻_P(u) ≤ m`,*

    |S| ≥ ν/2 - m                                                    (10.4)

*A similar argument yields*

    |T| ≥ ν/2 - m                                                    (10.5)

*Note that, by (10.2), both `S` and `T` are nonempty.  Adding (10.4) and (10.5) and
using (10.1), we obtain `|S| + |T| ≥ l - m + 1` and therefore, by (10.3),*

    |S ∪ T| ≥ l - m + 1                                              (10.6)

*Since `S` and `T` are disjoint and nonempty, there are positive integers `i` and
`k` such that `i ∈ S`, `i + k ∈ T` and*

    i + j ∉ S ∪ T   for   1 ≤ j < k                                  (10.7)

*where addition is taken modulo `l`.  From (10.6) and (10.7) we see that `k ≤ m`.
Thus the directed cycle `C_{i+k,i-1}(v_{i-1}, u)P(v, v_{i+k})`, which has length
`l + m + 1 - k`, is longer than `C`.  This contradiction establishes the theorem.*

**Skeleton** (for `∃ u p, IsDirectedCycle p ∧ p.length = ν`).  Follow the book, but
note the arithmetic is all over `ℕ` here, so each displayed inequality needs a
truncation-free restatement.
1. `by_contra`: no directed Hamilton cycle.  Take `C` a longest directed cycle,
   length `l`; exercise 10.1.7 with `k ≥ ν/2` gives `2l > ν` (the book's `l > ν/2`).
2. Take `P` a longest directed path in `D.induce (V(C))ᶜ`, origin `u`, terminus `v`,
   length `m`.  Record (10.1) as `l + m + 1 ≤ ν` and (10.2) as `2m < ν`.
3. **`S`, `T` as `Finset (Fin l)`** — indices into `C`, with `+1` modulo `l`, which
   is why `Fin l` is the right index type rather than `ℕ`.
4. **Disjointness (10.3).**  An index in both splices `P` into `C` for a cycle of
   length `l + m + 1 > l`, contradicting maximality of `C`.
5. **Size bounds (10.4)–(10.5).**  Maximality of `P` confines `N⁻(u)` to
   `V(P) ∪ V(C)`; subtract the `≤ m` in-neighbours inside `P` from
   `d⁻(u) ≥ ν/2` to bound `|S|`.  Symmetrically for `T` with `N⁺(v)`.
6. **The gap (10.6)–(10.7).**  From `|S ∪ T| ≥ l - m + 1` and disjointness, some
   `i ∈ S` has the next element of `S ∪ T` cyclically at distance `k ≤ m`, landing
   in `T`.  *This is the pigeonhole step and the fiddliest part* — it is a statement
   about gaps in a subset of `Fin l` of known size.
7. Splice along that gap for a cycle of length `l + m + 1 - k > l`; contradiction.

**Reading.**  The directed extension of Dirac's theorem 4.3 — a large minimum degree,
now in *both* directions, forces a spanning cycle.  Exercise 10.3.1 recovers Dirac
from it by orienting a graph suitably.

**Formalisation.**  `hdeg` states `ν ≤ 2 d⁻(v)` and `ν ≤ 2 d⁺(v)` rather than
`min{δ⁻,δ⁺} ≥ ν/2`, avoiding division; `hv : 2 < ν` is the book's `ν/2 > 1`.  The
result is only a *special case* of Ghouila-Houri's theorem, as B&M note. -/
theorem ghouila_houri_directed_hamilton_cycle
    {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (hstrict : D.IsStrict)
    (hv : 2 < Fintype.card V)
    (hdeg : ∀ v : V, Fintype.card V ≤ 2 * D.indegree v ∧ Fintype.card V ≤ 2 * D.outdegree v) :
    ∃ (u : V) (p : @Quiver.Path V D.toQuiver u u),
      D.IsDirectedCycle p ∧ @Quiver.Path.length V D.toQuiver u u p = Fintype.card V := by
  sorry

-- Ex 10.3.2: directed Euler tour ⇔ connected ∧ `d⁺ = d⁻` — build early, §10.5 depends on it.
/-- **Exercise 10.3.2.**  *`D` contains a directed Euler tour if and only if `D` is
connected and `d⁺(v) = d⁻(v)` for all `v ∈ V`.*

**Book proof.**  None — an exercise.

**⚠ Statement defect (read before filling).**  As stated the `↔` is **false**, for
two compounding reasons.

*The counterexample.*  Let `D` have no arcs at all and `card V ≥ 2`.  Then
`Quiver.Path.nil` at any `u` satisfies `IsDirectedEulerTour` vacuously — its arc
list is `[]` (`Nodup`), and there is no arc to exhaust — so the left side holds.
But `toSimpleGraphInclusive D = ⊥`, which is not `Connected` on `≥ 2` vertices,
while `outdegree = indegree = 0` everywhere; so the right side fails.

*Why.*  B&M's directed walks are explicitly **non-null** (§10.1), so `nil` is not a
directed tour for them and the degenerate case never arises.  `Quiver.Path.nil` is
available here, and `IsDirectedEulerTour` does not exclude it.

*The repair* has two parts: add `0 < Quiver.Path.length p` to
`IsDirectedEulerTour`, and then guard this statement against the *other* degenerate
case it creates — a one-vertex arcless digraph, where the right side holds
(trivially connected and balanced) but no positive-length tour exists.  A hypothesis
that `D` has at least one arc handles both.  **The skeleton assumes both repairs**,
and assumes `arcsOf` has been given its honest body.

**Skeleton.**
*(⇒) necessity.*
1. Each visit of the tour to a vertex consumes one incoming and one outgoing arc, so
   for every `v` the tour's arc list contains equally many arcs with head `v` as with
   tail `v`.
2. It uses every arc exactly once (`Nodup` plus the exhaustiveness clause), so those
   counts are `indegree v` and `outdegree v`.
3. Connectivity: every arc lies on the tour, and the tour is a single walk, so all
   arc-incident vertices lie in one component.

*(⇐) sufficiency.*
4. Take a **longest closed directed trail** `T`.
5. If `T` misses an arc, the balance condition lets one build a further closed
   directed trail in the remaining arcs, and connectivity places it meeting `T`;
   splice the two at a shared vertex for a longer closed trail — contradiction.
   This is theorem 4.1's argument with in/out degrees in place of parity.

**Reading.**  The directed analogue of Euler's theorem 4.1.  Every visit uses one
arrow in and one out, so the two counts must balance.  *Why it is built early:*
§10.5 depends on it — the de Bruijn digraph `D_n` is connected with every indegree
and outdegree `2`, so it has a directed Euler tour, and that tour is exactly the
binary sequence for the computer drum.

**Formalisation.**  Connectivity is asked of `toSimpleGraphInclusive`, the underlying
graph, matching B&M's "`D` is connected" (a property of the underlying graph, per
§10.1).

✅ **Statement repaired — connectivity moved from the right-hand side into a
hypothesis.**  As previously written, `(∃ Euler tour) ↔ (Connected ∧ balanced)`, the
`↔` was **false**, for two compounding reasons.

*Counterexample 1.*  Let `D` have no arcs and `card V ≥ 2`.  Then `Quiver.Path.nil` at
any `u` satisfies `IsDirectedEulerTour` — its arc list is `[]` (so `Nodup`), and the
exhaustiveness clause `∀ a b, D.Adj a b → …` is vacuous — so the left side holds,
while the right side fails because `D` is disconnected.

*Counterexample 2.*  Adding arcs does not rescue it: take one directed cycle plus an
isolated vertex.  A tour of the cycle exhausts every arc, so the left side holds, but
the underlying graph is still disconnected.

So no strengthening of the left side repairs this; connectivity has to be assumed, not
concluded.  With `hconn` a hypothesis the equivalence is the honest directed Euler
theorem, and it now matches the shape of this library's undirected
`euler_tour_iff_no_odd_degree` in `EulerHamilton.lean`.

⚠ Note that unlike the undirected statement, **no arc-nonemptiness hypothesis is
needed**: `hconn` already forces the arc-free case to be the one-vertex graph, where
`nil` is an Euler tour and the balance condition holds vacuously, so the `↔` is true
there. -/
theorem exists_directedEulerTour_iff
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (hconn : D.toSimpleGraphInclusive.Connected) :
    (∃ (u : V) (p : @Quiver.Path V D.toQuiver u u), D.IsDirectedEulerTour p) ↔
      (∀ v : V, D.outdegree v = D.indegree v) := by
  sorry

-- Ex 10.3.3: `l` arc-disjoint directed `(x,y)`-paths.
-- NOTE: B&M's proof adds `l` parallel arcs `(y,x)`, impossible in `Digraph`; the intended route works
-- on `Digraph (V ⊕ Fin l)`.  The statement itself stays on `D` and is well-typed here.
/-- **Exercise 10.3.3.**  *Let `D` be a digraph such that (i)
`d⁺(x) - d⁻(x) = l = d⁻(y) - d⁺(y)` and (ii) `d⁺(v) = d⁻(v)` for
`v ∈ V \ {x, y}`.  Show, using exercise 10.3.2, that there exist `l` arc-disjoint
directed `(x, y)`-paths in `D`.*

**Book proof.**  None — an exercise, but the route is prescribed ("using exercise
10.3.2").

**Skeleton** (for `l` arc-disjoint directed `(x,y)`-paths).
1. **Balance the digraph.**  Add `l` arcs from `y` back to `x`.  Every vertex is then
   balanced: `x` gains `l` incoming, `y` gains `l` outgoing, and `hrest` covers the
   others.
2. **Euler tour.**  Exercise 10.3.2 applies to the enlarged digraph — connectivity
   needs checking, and is where the construction can fail if `D` is disconnected;
   restrict to the component containing `x` and `y`.
3. **Cut the tour.**  Deleting the `l` added arcs cuts the closed tour into exactly
   `l` directed `(x, y)`-walks, pairwise arc-disjoint since the tour used each arc
   once.
4. **Walks to paths.**  Reduce each walk to a path (`bypass`-style), which only
   removes arcs and so preserves arc-disjointness.

**Reading.**  The degree conditions say `x` has an excess of `l` outgoing arcs, `y`
an excess of `l` incoming ones, and everything else is balanced — so `l` units of
"flow" must run from `x` to `y`.  A small precursor of the max-flow min-cut
machinery of chapter 11.

**Formalisation.**  ⚠ Two obstructions to the intended route, both recorded rather
than resolved.  (i) `Digraph` admits **no parallel arcs**, so step 1's "`l` copies of
`(y,x)`" is not expressible on `D`; the construction has to move to
`Digraph (V ⊕ Fin l)`, routing each extra arc through its own new vertex.  The
*statement* stays on `D` and is well-typed.  (ii) The conclusion mentions `arcsOf`,
which currently has a `sorry` body, so the arc-disjointness clause is presently
meaningless — see that definition.  Degrees are compared in `ℤ` to let `hx`, `hy`
state genuine differences without ℕ-truncation. -/
theorem exists_arcDisjoint_directedPaths
    {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    {x y : V} (hxy : x ≠ y) {l : ℕ}
    (hx : (D.outdegree x : ℤ) - D.indegree x = l)
    (hy : (D.indegree y : ℤ) - D.outdegree y = l)
    (hrest : ∀ v : V, v ≠ x → v ≠ y → D.outdegree v = D.indegree v) :
    ∃ ps : Fin l → Σ (u v : V), @Quiver.Path V D.toQuiver u v,
      (∀ i, (ps i).1 = x ∧ (ps i).2.1 = y) ∧
      (∀ i, D.IsDirectedPath (ps i).2.2) ∧
      (∀ i j, i ≠ j → List.Disjoint (D.arcsOf (ps i).2.2) (D.arcsOf (ps j).2.2)) := by
  sorry

-- Ex 10.3.4*: a diconnected digraph containing an odd cycle contains a directed odd cycle.
/-- **Exercise 10.3.4***.  *A diconnected digraph which contains an odd cycle also
contains a directed odd cycle.*

**Book proof.**  None — an exercise, and one the book **stars**.

**Skeleton** (for `∃ w p, IsDirectedCycle p ∧ Odd p.length`).
1. `by_contra`: assume every directed cycle of `D` has even length.
2. **Parity is well defined.**  Fix a base vertex `r`.  For each `v`, all directed
   `(r, v)`-walks have the same length parity: two of them of different parities
   would, with a return walk `v ⇝ r` (diconnection), yield two closed directed walks
   of different parities, hence a closed directed walk of odd length, hence — by
   decomposing it into directed cycles — an odd directed cycle, contradicting step 1.
   *This decomposition is the technical heart* and is worth its own lemma.
3. **2-colour.**  Set `c v :=` that common parity.  Diconnection makes `c` total.
4. **The colouring is proper on the underlying graph.**  For an edge `uv` of the
   underlying graph there is an arc one way or the other, and appending it flips
   parity, so `c u ≠ c v`.
5. So the underlying graph is bipartite, hence has no odd cycle (theorem 1.2) —
   contradicting `hc`, `hodd`.

**Reading.**  The hypothesis gives an odd cycle in the *underlying* graph, whose arcs
may point every which way; the conclusion upgrades it to a genuinely directed odd
cycle.  Diconnection is essential — without it the parity argument cannot be
propagated across the whole digraph, and the statement is false.

**Formalisation.**  The undirected cycle enters as a `Walk` in
`toSimpleGraphInclusive` with `IsCycle` and `Odd length`; the directed conclusion is
a `Quiver.Path`.  Step 2's "decompose a closed walk into directed cycles" has no
Mathlib counterpart for `Quiver.Path` and will have to be built. -/
theorem exists_directed_odd_cycle
    {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (hdicon : D.Diconnected)
    {u : V} {c : D.toSimpleGraphInclusive.Walk u u} (hc : c.IsCycle) (hodd : Odd c.length) :
    ∃ (w : V) (p : @Quiver.Path V D.toQuiver w w),
      D.IsDirectedCycle p ∧ Odd (@Quiver.Path.length V D.toQuiver w w p) := by
  sorry

-- Ex 10.3.5: a nontrivial digraph is diconnected ⇔ 1-arc-connected.
/-- **Exercise 10.3.5.**  *A nontrivial digraph is diconnected if and only if it is
1-arc-connected.*

**Book proof.**  None — an exercise.

**Skeleton** (for `D.Diconnected ↔ D.IsKArcConnected 1`).

*(⇒).*
1. Let `S` be nonempty and proper; pick `u ∈ S` and `w ∉ S`.
2. Diconnection gives `Reachable u w`; along that chain there is a first vertex
   outside `S`, so some arc runs from `S` to `Sᶜ`.  Hence `1 ≤ |(S, Sᶜ)|`.
   (`ReflTransGen.head_induction_on` gives the "first exit" cleanly.)

*(⇐).*
3. Fix `u` and let `S := {w | D.Reachable u w}`, a `Finset` via decidability.  It is
   nonempty (`u ∈ S`, by reflexivity).
4. **`S` is closed under arcs**: if `w ∈ S` and `D.Adj w z` then `z ∈ S`.  So
   `|(S, Sᶜ)| = 0`.
5. By `IsKArcConnected 1`, `S` cannot be both nonempty and proper — so `S = univ`,
   i.e. `u` reaches everything.  As `u` was arbitrary, `D` is diconnected.

**Reading.**  Diconnection is the `k = 1` case of arc-connectivity, exactly as
connection is the `k = 1` case of edge-connectivity in §3.1.

**Formalisation.**  `[Nontrivial V]` is the book's "nontrivial digraph" and is
load-bearing: on a one-vertex carrier there is no nonempty proper `S`, so
`IsKArcConnected 1` is vacuously true while `Diconnected` — which is also true there
— would make the `↔` hold only by accident.  More importantly, its absence is what
breaks `associatedDigraph_isKArcConnected_iff` below. -/
theorem diconnected_iff_isKArcConnected_one
    {V : Type*} [Fintype V] [Nontrivial V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj] :
    D.Diconnected ↔ D.IsKArcConnected 1 := by
  sorry

open scoped Classical in
-- Ex 10.3.6(b): `D(G)` is `k`-arc-connected ⇔ `G` is `k`-edge-connected.
/-- **Exercise 10.3.6(b).**  *`D(G)` is `k`-arc-connected if and only if `G` is
`k`-edge-connected.*

**Book proof.**  None — an exercise.

**⚠ Statement defect (read before filling).**  The `↔` is **false** on a one-vertex
carrier.  Take `card V = 1`, so `G = ⊥` and `k = 1`.  *Left side:* there is no
nonempty proper `S : Finset V`, so `IsKArcConnected 1` holds vacuously.  *Right
side:* `G` has no edge cut at all (`⊥` on one vertex is `Connected`, so nothing
disconnects it), hence `edgeConnectivity G = sInf ∅ = 0`, and `1 ≤ 0` fails.

The cause is that `IsKArcConnected` drops B&M's standing **nontrivial** hypothesis
(exercise 10.3.5: *A nontrivial digraph `D` is `k`-arc-connected if…*).  The fix is
to add `[Nontrivial V]`, exactly as `diconnected_iff_isKArcConnected_one` next door
already does.  **The skeleton assumes it.**

**Skeleton** (for `G.associatedDigraph.IsKArcConnected k ↔ k ≤ edgeConnectivity G`).
1. **The pointwise bridge.**  For each nonempty proper `S`, the arcs of `D(G)` from
   `S` to `Sᶜ` correspond bijectively to the edges of `G` crossing between them:
   an edge `s(u,v)` with `u ∈ S`, `v ∉ S` gives exactly one arc `(u,v)` in that
   direction.  So `|(S, Sᶜ)| = |[S, Sᶜ]|`.  ⚠ Each crossing edge yields *two* arcs
   in `D(G)`, but only *one* of them lies in `(S, Sᶜ)` — the other is in `(Sᶜ, S)`.
   Getting this off by a factor of two is the obvious trap.
2. **(⇒).**  Given `IsKArcConnected k` and an edge cut `F` of `G`, take `S` a
   component of `G - F`; step 1 gives `k ≤ |[S, Sᶜ]| ≤ |F|`.  So `k` bounds every
   edge-cut size, hence `k ≤ sInf`, i.e. `k ≤ edgeConnectivity G`.
3. **(⇐).**  Given `k ≤ edgeConnectivity G` and a nonempty proper `S`, the edge set
   `[S, Sᶜ]` is an edge cut, so its size is `≥ edgeConnectivity G ≥ k`; step 1
   transfers this to `|(S, Sᶜ)|`.

**Reading.**  The associated digraph faithfully preserves connectivity, so the
directed notion generalises the undirected one.  Contrast §10.6, where the question
is which *orientations* — not the doubling — preserve it; there the answer is much
more delicate (Robbins, Nash-Williams).

**Formalisation.**  "`G` is `k`-edge-connected" is spelled `k ≤ edgeConnectivity G`,
per §3.1.  Step 2 needs that a minimal edge cut is `[S, Sᶜ]` for a component `S`,
which is the same fact the local `IsEdgeCut` docstring notes when reconciling the
book's shape-based definition with the deletion-based one used here.

✅ **Statement repaired — `[Nontrivial V]` added.**  The `↔` was **false on a
one-vertex carrier**.  Take `card V = 1`, so `G = ⊥`, and `k = 1`.  *Left side:* there
is no nonempty proper `S : Finset V`, so `IsKArcConnected 1` holds vacuously.  *Right
side:* `⊥` on one vertex is `Connected`, so nothing disconnects it, `G` has no edge cut
at all, and `edgeConnectivity G = 0`; the claim `1 ≤ 0` fails.

`[Nontrivial V]` excludes exactly that carrier and is the hypothesis the book's
"nontrivial digraph" convention supplies implicitly (compare
`diconnected_iff_isKArcConnected_one` above, which already carries it).  ⚠ Both Menger
statements in `Networks.lean` consume this lemma, so their hypotheses must be checked
against the added `Nontrivial` when they are proved. -/
theorem associatedDigraph_isKArcConnected_iff
    {V : Type*} [Fintype V] [Nontrivial V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) :
    G.associatedDigraph.IsKArcConnected k ↔ k ≤ edgeConnectivity G := by
  sorry

/-! ## §10.5 -/

open scoped Classical in
-- (10.5′): each vertex of `D_n` has indegree 2 and outdegree 2.
/-- **Book observation** (B&M §10.5, verbatim).  *Clearly, `D_n` is connected and each
vertex of `D_n` has indegree two and outdegree two.*

**Book proof.**  None — asserted as "clearly".

**Skeleton** (for `indegree v = 2 ∧ outdegree v = 2`).
1. **Outdegree.**  The out-neighbours of `p` are the `q` with `q i = p ⟨i+1, _⟩` for
   all `i` with `i + 1 < n - 1`.  That pins every coordinate of `q` except the last,
   which is free — so the out-neighbour set is in bijection with `Bool`.  Build that
   equivalence explicitly and take `card`.
2. **Indegree.**  Dually: the in-neighbours of `q` are the `p` agreeing with `q` on a
   shifted range, with `p 0` free — again two.
3. Each is a `Finset.card` of a filter over `Fin (n-1) → Bool`; the clean route is
   to exhibit the two elements and show the filter equals `{q₀, q₁}` with
   `q₀ ≠ q₁` (they differ in the free coordinate — which needs `n - 1 ≥ 1`, i.e.
   `hn : 2 ≤ n`).

**Reading.**  A vertex is a window of `n-1` bits.  Its out-neighbours drop the
leading bit and append a new one — two choices; its in-neighbours drop the trailing
bit and prepend a new one — again two.  This is the balance condition exercise
10.3.2 needs, and is why `D_n` has a directed Euler tour.

**Formalisation.**  `hn : 2 ≤ n` is load-bearing in step 3: for `n = 1` the carrier
`Fin 0 → Bool` is a singleton and the free coordinate does not exist, so the two
neighbours coincide and the degree is `1`, not `2`. -/
theorem deBruijnDigraph_indegree_eq_two (n : ℕ) (hn : 2 ≤ n) (v : Fin (n-1) → Bool) :
    (deBruijnDigraph n).indegree v = 2 ∧ (deBruijnDigraph n).outdegree v = 2 := by
  sorry

-- (10.5′): `D_n` is connected.
/-- **Book observation** (B&M §10.5, verbatim).  *Clearly, `D_n` is connected…*

**Book proof.**  None — asserted as "clearly".

**Skeleton** (for `(deBruijnDigraph n).toSimpleGraphInclusive.Connected`).
1. **Prove the stronger fact first: `D_n` is diconnected.**  From `p`, reaching `q`
   takes exactly `n - 1` shifts — at step `i`, shift in `q`'s `i`-th bit.  Formally,
   define the intermediate windows explicitly and check each consecutive pair is an
   arc.
2. Connectivity of the underlying graph follows, since a directed walk projects to
   an undirected one, plus `Nonempty` (the carrier `Fin (n-1) → Bool` is nonempty).
3. The book only needs connectivity for exercise 10.3.2, so step 1 is more than
   required — but it is no harder, and diconnection is the fact worth having.

**Reading.**  From any binary string one can reach any other by shifting in the
target's bits one at a time; after `n - 1` shifts the window contains exactly the
target.  Together with the degree balance above, this is the second half of the
Euler-tour criterion of exercise 10.3.2.

**Formalisation.**  The explicit walk of step 1 is the whole content; a slick
argument is unlikely to be shorter than just writing the `n - 1` intermediate
vertices down as a function of the step index. -/
theorem deBruijnDigraph_connected (n : ℕ) (hn : 2 ≤ n) :
    (deBruijnDigraph n).toSimpleGraphInclusive.Connected := by
  sorry

-- (10.5′): `D_n` has a directed Euler tour.
/-- **Book conclusion (§10.5).**  *Therefore (exercise 10.3.2) `D_n` has a directed
Euler tour.  This directed Euler tour, regarded as a sequence of arcs of `D_n`,
yields a binary sequence of length `2ⁿ` suitable for the design of the drum
surface.*

**Book proof.**  The quoted passage *is* the argument: connectivity plus balanced
degrees, then exercise 10.3.2.

**Skeleton** (for `∃ u p, IsDirectedEulerTour p`).
1. `deBruijnDigraph_connected` supplies the connectivity conjunct.
2. `deBruijnDigraph_indegree_eq_two` supplies `outdegree v = indegree v` (both `2`).
3. Apply `exists_directedEulerTour_iff` in the `⇐` direction.

**Reading.**  Each arc carries an `n`-bit label and the tour uses every arc exactly
once, so reading off the first digit of each label in order produces a cyclic binary
sequence of length `2ⁿ` in which all `2ⁿ` windows of length `n` are distinct.

*The application.*  Divide a rotating drum's surface into `2ⁿ` sections according to
that sequence; then `n` consecutive contacts read a different `n`-bit number at each
of the `2ⁿ` positions, so all positions are distinguishable — and `n` is optimal,
since `k` contacts give only `2ᵏ` readings.  For `n = 4` the book's tour gives
`0000111100101101`.  Due to Good (1946).

**Formalisation.**  ⚠ This is a three-line consequence of its two inputs, but it
inherits both defects of `exists_directedEulerTour_iff`: that theorem is currently
false as stated, and `IsDirectedEulerTour` is defined through the `sorry`-bodied
`arcsOf`.  Until those are repaired this statement is not the intended one.  Note
also that the *labels* are not modelled — the conclusion asserts a tour exists, and
turning it into the binary sequence is left to `exists_deBruijn_sequence`. -/
theorem deBruijnDigraph_exists_directedEulerTour (n : ℕ) (hn : 2 ≤ n) :
    ∃ (u : Fin (n-1) → Bool) (p : @Quiver.Path _ (deBruijnDigraph n).toQuiver u u),
      (deBruijnDigraph n).IsDirectedEulerTour p := by
  sorry

-- DROPPED: Ex 10.5.1 — "find a circular sequence…": a specific computation, not a proposition.

/-! ## §10.6 -/

-- Thm 10.5 (Robbins): a 2-edge-connected graph has a diconnected orientation.
-- NOTE: rides ch3 exercise 3.2.1 (edge-disjoint paths to a subgraph), absent from Mathlib and repo.
/-- **Theorem 10.5** (Robbins, 1939).  *If `G` is 2-edge-connected, then `G` has a
diconnected orientation.*

**Book proof** (B&M §10.6, verbatim).  *Let `G` be 2-edge-connected.  Then `G`
contains a cycle `G₁`.  We define inductively a sequence `G₁, G₂, …` of connected
subgraphs of `G` as follows: if `Gᵢ (i = 1, 2, …)` is not a spanning subgraph of
`G`, let `vᵢ` be a vertex of `G` not in `Gᵢ`.  Then (exercise 3.2.1) there exist
edge-disjoint paths `Pᵢ` and `Qᵢ` from `vᵢ` to `Gᵢ`.  Define*

    G_{i+1} = Gᵢ ∪ Pᵢ ∪ Qᵢ

*Since `ν(G_{i+1}) > ν(Gᵢ)`, this sequence must terminate in a spanning subgraph
`G_n` of `G`.*

*We now orient `G_n` by orienting `G₁` as a directed cycle, each path `Pᵢ` as a
directed path with origin `vᵢ`, and each path `Qᵢ` as a directed path with terminus
`vᵢ`.  Clearly every `Gᵢ`, and hence in particular `G_n`, is thereby given a
diconnected orientation.  Since `G_n` is a spanning subgraph of `G` it follows that
`G`, too, has a diconnected orientation.*

**Skeleton** (for `∃ D, IsOrientationOf G ∧ D.Diconnected`).
1. **Get a cycle.**  `2 ≤ κ'` forces `δ ≥ 2`, hence a cycle `G₁`.
2. **The ear decomposition.**  Induct on the number of vertices outside `Gᵢ`.  Given
   `vᵢ ∉ Gᵢ`, exercise 3.2.1 supplies **edge-disjoint** paths `Pᵢ`, `Qᵢ` from `vᵢ`
   to `Gᵢ`.  ⚠ This is the load-bearing import and is **absent from Mathlib and the
   repo** — it must be proved first, and is itself a real piece of connectivity
   theory (it is the two-edge-disjoint-paths form of Menger).
3. **Orient each ear.**  `G₁` as a directed cycle; `Pᵢ` directed *out of* `vᵢ`;
   `Qᵢ` directed *into* `vᵢ`.
4. **Diconnection is preserved.**  Induct: `Gᵢ` diconnected plus a way out of and a
   way into `vᵢ` makes `G_{i+1}` diconnected.  This is the mathematical content.
5. **Extend to all of `G`.**  `G_n` is spanning, so orienting the remaining edges
   arbitrarily leaves every vertex reachable from every other.

**Reading.**  How to make a road system one-way so traffic can still flow
everywhere.  A graph with a cut edge clearly cannot manage it — whichever way that
edge is directed, one side becomes unreachable — and Robbins showed
2-edge-connectivity is not merely necessary but sufficient.  Intuitively, each new
vertex is given both a way in and a way out.

**Formalisation.**  ⚠ Step 2 rides chapter 3's exercise 3.2.1, which this repo does
not have; budget for it before starting.  `h2ec : 2 ≤ edgeConnectivity G` is
"`2`-edge-connected" per §3.1.  Theorem 10.6 is the `k = 1` case of a different
route to the same conclusion, so neither theorem subsumes the other. -/
theorem robbins_orientation
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h2ec : 2 ≤ edgeConnectivity G) :
    ∃ D : Digraph V, D.IsOrientationOf G ∧ D.Diconnected := by
  sorry

open scoped Classical in
-- Thm 10.6: a `2k`-edge-connected graph with an Euler trail has a `k`-arc-connected orientation.
/-- **Theorem 10.6.**  *Let `G` be a `2k`-edge-connected graph with an Euler trail.
Then `G` has a `k`-arc-connected orientation.*

**Book proof** (B&M §10.6, verbatim).  *Let `v₀ e₁ v₁ … e_ε v_ε` be an Euler trail
of `G`.  Orient `G` by converting the edge `eᵢ` with ends `v_{i-1}` and `vᵢ` to an
arc `aᵢ` with tail `v_{i-1}` and head `vᵢ`, for `1 ≤ i ≤ ε`.  Now let `[S, S̄]` be an
`m`-edge cut of `G`.  The number of times the directed trail
`(v₀, a₁, v₁, …, a_ε, v_ε)` crosses from `S` to `S̄` differs from the number of times
it crosses from `S̄` to `S` by at most one.  Since it includes all arcs of `D`, both
`(S, S̄)` and `(S̄, S)` must contain at least `[m/2]` arcs.  The result follows.*

**Skeleton** (for `∃ D, IsOrientationOf G ∧ D.IsKArcConnected k`).
1. **Orient along the trail.**  `ht : t.IsEulerian` gives a walk using every edge
   exactly once; define `D.Adj u v` to hold when `(u,v)` occurs as a step of `t`.
   Well defined and an orientation because each edge is traversed once, in one
   direction.
2. **Crossings alternate.**  For a fixed `S`, walking along `t` the side alternates:
   between two consecutive `S → S̄` crossings there must be an `S̄ → S` crossing.  So
   `| #(S→S̄) - #(S̄→S) | ≤ 1`.  *This is the heart* and is a statement about the
   list of vertices of `t`, best proved by induction along it.
3. **Every crossing edge is an arc one way or the other.**  Since `t` uses every
   edge, `#(S→S̄) + #(S̄→S) = m`, where `m = |[S, Sᶜ]|`.
4. **Combine.**  Steps 2 and 3 give `#(S→S̄) ≥ ⌊m/2⌋`, i.e. `2 * #(S→S̄) + 1 ≥ m`.
5. **Feed the hypothesis.**  `h2k : 2k ≤ κ'` and `[S, Sᶜ]` being an edge cut give
   `m ≥ 2k`, so `#(S→S̄) ≥ k`.  That is `IsKArcConnected k`.

**Reading.**  The easy special case of a theorem of Nash-Williams (1960), that
*every* `2k`-edge-connected graph has a `k`-arc-connected orientation; the general
proof is difficult.  Robbins' theorem 10.5 is the case `k = 1` — proved there by a
quite different, ear-decomposition route.

**Formalisation.**  ⚠ Step 4's `⌊m/2⌋` is stated as `2 * count + 1 ≥ m` to keep ℕ
division out.  Step 2 is where an Euler *trail* rather than a tour matters: an open
trail is what allows the discrepancy of one, and a closed tour would give equality.
Note `t : G.Walk u v` with `u`, `v` unconstrained, so both cases are covered. -/
theorem exists_kArcConnected_orientation_of_eulerian
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (h2k : 2 * k ≤ edgeConnectivity G)
    {u v : V} {t : G.Walk u v} (ht : t.IsEulerian) :
    ∃ D : Digraph V, D.IsOrientationOf G ∧ D.IsKArcConnected k := by
  sorry

-- DROPPED: Ex 10.6.1 (Petersen refutes balanced-orientability) — recommend DROP for budget: negative
-- result, needs a from-scratch `petersenGraph`, only tractable via `native_decide`; no reusable math.

-- DROPPED: Ex 10.6.2(a) — rides Nash-Williams' theorem (unproved in B&M) + ch12 bonds.

-- DROPPED: Ex 10.6.2(b) — cites figure 8.2 (Grötzsch graph), out of chapter.

/-! ## §10.7 -/

-- Thm 10.7: for a diconnected tournament with `ν ≥ 5`, `A^{d+3}` is entrywise positive.
/-- **Theorem 10.7.**  *Let `D` be a diconnected tournament with `ν ≥ 5`, and let `A`
be the adjacency matrix of `D`.  Then `A^{d+3} > 0` (every entry positive), where
`d` is the directed diameter of `D`.*

**Book proof** (B&M §10.7, verbatim).  *The `(i,j)`th entry of `Aᵏ` is precisely the
number of directed `(vᵢ, vⱼ)`-walks of length `k` in `D` (exercise 10.1.8).  We must
therefore show that, for any two vertices `vᵢ` and `vⱼ` (possibly identical), there
is a directed `(vᵢ, vⱼ)`-walk of length `d+3`.*

*Let `d_ij = d⃗(vᵢ, vⱼ)`.  Then `0 ≤ d_ij ≤ d ≤ ν - 1` and therefore*

    3 ≤ d - d_ij + 3 ≤ ν + 2

*If `d - d_ij + 3 ≤ ν` then, by theorem 10.3, there is a directed
`(d - d_ij + 3)`-cycle `C` containing `vⱼ`.  A directed `(vᵢ, vⱼ)`-path `P` of
length `d_ij` followed by the directed cycle `C` together form a directed
`(vᵢ, vⱼ)`-walk of length `d+3`, as desired.*

*There are two special cases.  If `d - d_ij + 3 = ν + 1`, then `P` followed by a
directed `(ν - 2)`-cycle through `vⱼ` followed by a directed 3-cycle through `vⱼ`
constitute a directed `(vᵢ, vⱼ)`-walk of length `d+3` (the `(ν - 2)`-cycle exists
since `ν ≥ 5`); and if `d - d_ij + 3 = ν + 2`, then `P` followed by a directed
`(ν - 1)`-cycle through `vⱼ` followed by a directed 3-cycle through `vⱼ` constitute
such a walk.*

**Skeleton** (for `∀ i j, 0 < (A ^ (d + 3)) i j`).
1. **Reduce to walk existence** by exercise 10.1.8: the entry is
   `Nat.card {p : Path i j // length p = d + 3}`, so positivity is exactly
   "there is such a walk" (plus finiteness of the subtype).
2. **Set `dᵢⱼ := dirDist i j`.**  Diconnection makes it attained by an actual path
   `P`, and `dᵢⱼ ≤ d` by definition of `dirDiameter`.
3. **Case `d - dᵢⱼ + 3 ≤ ν`.**  Moon's theorem 10.3 gives a directed cycle through
   `j` of exactly that length (it is `≥ 3` since `dᵢⱼ ≤ d`).  Concatenate `P` with
   it: total length `dᵢⱼ + (d - dᵢⱼ + 3) = d + 3`.
4. **Case `= ν + 1`.**  `P`, then a `(ν-2)`-cycle through `j`, then a `3`-cycle
   through `j`: `dᵢⱼ + (ν - 2) + 3 = d + 3`.  Both cycles exist by theorem 10.3,
   using `ν ≥ 5` to keep `ν - 2 ≥ 3`.
5. **Case `= ν + 2`.**  Same with a `(ν-1)`-cycle.
6. Note all three cases concatenate *walks*, not paths — repetition is fine and
   indeed necessary.

**Reading.**  *Why it matters (§10.7).*  The `i`-th level score vector of a
tournament is `sᵢ = AⁱJ`, each player's score being the sum of the scores of those
they beat.  Primitivity of `A` is what lets Perron–Frobenius guarantee these vectors
converge to a positive eigenvector, giving a well-defined ranking.

**Formalisation.**  ⚠ The arithmetic `d - dᵢⱼ + 3` is ℕ-subtraction but never
truncates, since `dᵢⱼ ≤ d`; still, establish that inequality before the case split
rather than relying on it implicitly.  `ν ≥ 5` is load-bearing in step 4 only. -/
theorem tournament_adjMatrix_pow_pos
    {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (htour : D.IsTournament) (hdicon : D.Diconnected) (hv : 5 ≤ Fintype.card V) :
    ∀ i j : V, 0 < (D.adjMatrix ℕ ^ (D.dirDiameter + 3)) i j := by
  sorry

-- Cor 10.7: a tournament's adjacency matrix is primitive ⇔ diconnected ∧ `ν ≥ 4`.
/-- **Corollary 10.7.**  *The adjacency matrix `A` of a tournament `D` is primitive
if and only if `D` is diconnected and `ν ≥ 4`.*

**Book proof** (B&M §10.7, verbatim).  *If `D` is not diconnected, then there are
vertices `vᵢ` and `vⱼ` in `D` such that `vⱼ` is not reachable from `vᵢ`.  Thus there
is no directed `(vᵢ, vⱼ)`-walk in `D`.  It follows that the `(i,j)`th entry of `Aᵏ`
is zero for all `k`, and hence `A` is not primitive.*

*Conversely, suppose that `D` is diconnected.  If `ν ≥ 5` then, by theorem 10.7,
`A^{d+3} > 0` and so `A` is primitive.  There is just one diconnected tournament on
three vertices (figure 10.14a), and just one diconnected tournament on four vertices
(figure 10.14b).  It is readily checked that the adjacency [matrices behave as
claimed].*

**Skeleton** (for `IsPrimitive A ↔ (Diconnected ∧ 4 ≤ ν)`).

*(⇒).*
1. **Not diconnected ⟹ not primitive.**  Unreachable `vⱼ` from `vᵢ` means no
   directed walk, so by exercise 10.1.8 every `(Aᵏ) i j = 0`.
2. **`ν ≤ 3` ⟹ not primitive.**  Enumerate: `ν ≤ 2` tournaments have a vertex of
   outdegree `0`; the unique diconnected `3`-tournament is the directed triangle,
   whose `Aᵏ` is a cyclic permutation matrix and never positive.  ⚠ The book
   asserts this by inspection of figure 10.14a — the figure is omitted from the
   source, so the `3`-vertex case must be reconstructed, not quoted.

*(⇐).*
3. **`ν ≥ 5`**: theorem 10.7 gives `A^{d+3} > 0` directly.
4. **`ν = 4`**: the unique diconnected `4`-tournament, whose `A⁹` is entrywise
   positive.  Again figure 10.14b is omitted; identify the tournament up to
   isomorphism (it is the one with score sequence `(1,1,1,3)` — check) and compute.
   `decide` over a `4`-element carrier is plausible here.

**Reading.**  *The ranking method (§10.7).*  When `A` is primitive, Perron–Frobenius
gives a largest real eigenvalue `r` with `lim_i (A/r)ⁱ J = s`, a positive
eigenvector; the normalised `s̄` measures relative strengths.  For the book's
six-player example `r ≈ 2.232` and `s̄ ≈ (.238, .164, .231, .113, .150, .104)`,
ranking the players `1, 3, 2, 5, 4, 6`.  Non-diconnected tournaments are handled by
ranking within dicomponents and then ordering the dicomponents by dominance
(exercises 10.1.9 and 10.1.3(b)).  Due to Wei (1952) and Kendall (1955).

**Formalisation.**  ⚠ Steps 2 and 4 are the awkward ones: B&M discharge them by
pointing at a figure the source omits, so the two small tournaments have to be
identified and checked from scratch.  Everything else follows from theorem 10.7 and
exercise 10.1.8. -/
theorem tournament_adjMatrix_isPrimitive_iff
    {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]
    (htour : D.IsTournament) :
    (D.adjMatrix ℕ).IsPrimitive ↔ (D.Diconnected ∧ 4 ≤ Fintype.card V) := by
  sorry

-- DROPPED: Ex 10.7.1(a) — cites the omitted figure 10.4; not text-determined.

-- DROPPED: Ex 10.7.1(b) — numeric eigenvector computation needing Perron–Frobenius (0 hits).

-- DROPPED: Ex 10.7.2(a),(b) — the ranking method is procedural + needs Perron–Frobenius.

