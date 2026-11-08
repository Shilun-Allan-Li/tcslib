import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Lattice

/-!
# Bondy & Murty, *Graph Theory with Applications* — Chapter 9: Planar Graphs

Sorry-skeleton extracted from `papers/bondy-murty-ch9-planar-graphs.md`.

**Scope.** Mathlib has *no* planarity: no `IsPlanar`, no faces, no dual, no
Jordan-curve theorem, no Kuratowski, no minors/subdivisions.  Consequently ~85% of
Chapter 9 (Euler's formula, Kuratowski, the five/four-colour material, Grinberg,
the dual, the §9.8 algorithm, and essentially every numbered result) is *dropped*
— it is unstatable without an entire plane-topology library.  What survives is the
purely **combinatorial** core: §9.4 bridge theory (bridges of a subgraph as
equivalence classes of a walk relation, with Chvátal–Erdős as its prize), Tait
colourings (encoded exactly as `G.lineGraph.Colorable 3`), and two arithmetic cores
salvaged by restatement.  See the paper markdown for the full disposition.

Every proof body is `sorry`; this is a scaffold for sorry-driven development.
The connectivity API (`IsVertexCut`, `vertexConnectivity`) is defined locally,
mirroring `TCSlib/GraphTheory/Connectivity.lean`: the outline's
`import TCSlib.GraphTheory.*` lines refer to repo files not imported here.

The scope claim above was re-checked against the Mathlib pinned in this repo:
`Mathlib/Combinatorics/SimpleGraph/` contains no planarity file, and the only
occurrence of "planar" anywhere under `Mathlib/Combinatorics/` is a passing
mention in `Coloring.lean`.  So the drop list stands.

## How each declaration is annotated

Every docstring below has a fixed shape, so that the book's own mathematics stays
separable from this file's formalisation choices:

1. **The book's own statement** (for a theorem) or **definition** (for a `def`),
   quoted verbatim from Bondy & Murty, with the LaTeX transcribed into
   Lean-style backticks.  Where the surviving Lean statement is a *restatement*
   (planarity traded for an arithmetic hypothesis), the book's original is still
   quoted and the substitution is recorded under **Formalisation**.
2. **Book proof** — B&M's printed proof, again verbatim.  Where the book gives no
   proof (every exercise, and the facts §9.4 calls "immediate") this is said
   explicitly rather than being filled in with a reconstruction.
3. **Skeleton** — an *abstract* plan, numbered, keyed to the Lean statement as it
   actually appears in this file.  Each step names the intermediate fact to be
   established and the Mathlib/local notion it is stated in; it deliberately does
   **not** commit to tactics.  The intent is that a step becomes one
   `have … := by sorry`, filled one at a time against `lake build`.
4. **Reading** — informal intuition: what the result means, why it is true, and
   how it sits among the chapter's other results (including the dropped ones,
   since the surviving core exists to serve them).
5. **Formalisation** — present only where the Lean statement departs from the
   book's, recording what was changed and why.

Definitions carry parts 1, 4 and 5 only: there is nothing to prove.

**Four declarations were defective and have been repaired**; each carries a `⚠`
block recording what changed, so the divergence from a naive transcription is not
mistaken for a slip.  In brief:

* `Overlaps` had a `sorry` body, which made theorem 9.6 vacuous.  It is now the
  honest negation of `Avoids`, and the segment machinery it needs — `cycleDist`,
  `Walk.OnArc`, `ConsecutiveAttach`, `Avoids` — has been added alongside it.  This
  is the layer B&M assume whenever they speak of *segments*.
* `bridgeOf_connected` and `exists_path_internallyDisjoint` were false for want of
  `e ∈ G.edgeSet \ H.edgeSet`, which is now a hypothesis of each.
* `succ_attachments_not_adj` (exercise 9.4.3(a)(ii)) was false because it dropped the
  book's standing assumption that `B` is the bridge from part (i); it now carries
  `hoff`, that bridge's defining property.  A `K₅` counterexample to the old form is
  recorded in its docstring.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Local connectivity API (mirrors `Connectivity.lean`; repo `Connectivity/Defs.lean`) -/

/-- A **vertex cut**: a subset `S` whose deletion leaves `G` disconnected.

**Book definition** (B&M §3.1, verbatim).  *A vertex cut of `G` is a subset `V'` of
`V` such that `G - V'` is disconnected.  A `k`-vertex cut is a vertex cut of `k`
elements.  A complete graph has no vertex cut; in fact, the only graphs which do
not have vertex cuts are those that contain complete graphs as spanning
subgraphs.*

**Reading.**  Deleting `V'` breaks the graph into pieces that no longer
communicate.  Needed here only to support `vertexConnectivity`, which the
Chvátal–Erdős theorem (exercise 9.4.3(b)) compares against the independence
number `α`.

**Formalisation.**  Mirrors `TCSlib/GraphTheory/Connectivity.lean`.  The conjunct
`↑S ⊂ Set.univ` excludes `S = V`, where the deleted graph has empty carrier:
Mathlib's `Connected` carries a `Nonempty` field, so without this guard every
graph would have `V` itself as a vertex cut. -/
def IsVertexCut (G : SimpleGraph V) (S : Finset V) : Prop :=
  (↑S : Set V) ⊂ Set.univ ∧ ¬ (G.induce ((↑S : Set V)ᶜ)).Connected

open scoped Classical in
/-- Vertex connectivity `κ(G)`: the minimum cut size, or `ν − 1` when no cut exists.

**Book definition** (B&M §3.1, verbatim).  *If `G` has at least one pair of distinct
nonadjacent vertices, the connectivity `κ(G)` of `G` is the minimum `k` for which
`G` has a `k`-vertex cut; otherwise, we define `κ(G)` to be `ν - 1`.  Thus
`κ(G) = 0` if `G` is either trivial or disconnected.  `G` is said to be
`k`-connected if `κ(G) ≥ k`.  All nontrivial connected graphs are 1-connected.*

**Reading.**  How many vertices must be removed to break the graph apart.  The
`ν - 1` branch is the convention that makes `κ(K_ν) = ν - 1`: a complete graph
cannot be disconnected by *any* vertex deletion, so the minimum would otherwise be
over an empty set.

**Formalisation.**  Mirrors the repo's `vertexConnectivity`
(`Connectivity/Defs.lean`).  The book splits on "has a pair of distinct nonadjacent
vertices"; this splits on the equivalent "has a vertex cut", which is the form the
`sInf` needs.  Note that `2 ≤ G.vertexConnectivity` is how "2-connected" is spelled
in exercise 9.6.7(b) below. -/
noncomputable def vertexConnectivity (G : SimpleGraph V) : ℕ :=
  if ∃ S : Finset V, G.IsVertexCut S then
    sInf {n : ℕ | ∃ S : Finset V, G.IsVertexCut S ∧ S.card = n}
  else
    Fintype.card V - 1

/-! ## §9.4 Key Definitions — the bridge apparatus (all honest bodies)

`SimpleGraph.IsBridge` (Mathlib) is B&M's *cut edge*, NOT §9.4's "bridge" (a subgraph).
The §9.4 bridge is an equivalence class of `E(G) \ E(H)` under a walk relation.  None of
this exists in Mathlib or the repo (0 hits); it is built here from scratch. -/

/-- A walk is **internally disjoint from** a subgraph `H`: no *internal* vertex lies in `H`.
⚠ NOT the repo's `InternallyDisjoint` (`TwoConnected.lean:58`), which is walk-vs-*walk*.

**Book definition** (B&M §9.4, verbatim).  *`W` is internally-disjoint from `H`
(that is, no internal vertex of `W` is a vertex of `H`).*

**Reading.**  The walk may start and end on `H`, but between those endpoints it
must stay entirely outside `H`.  This is what makes the bridge relation an
equivalence, and it is why a bridge is a maximal chunk of the graph hanging off
`H` and touching it only at its attachment points.

**Formalisation.**  `p.support.tail.dropLast` is the walk's interior — drop the
first vertex (`tail`) and the last (`dropLast`).  ⚠ This is **not** the repo's
`InternallyDisjoint` (`TwoConnected.lean:58`), which relates a walk to another
*walk*; here the second argument is a `Subgraph`.  A walk of length `≤ 1` has empty
interior and so is vacuously internally disjoint from everything — which is
intended, and is what makes `bridgeRel` reflexive on single edges. -/
def Walk.InternallyDisjointFrom {V : Type*} {G : SimpleGraph V}
    (H : G.Subgraph) {u v : V} (p : G.Walk u v) : Prop :=
  ∀ x ∈ p.support.tail.dropLast, x ∉ H.verts

/-- B&M's relation `~` on `E(G) \ E(H)`: `e₁ ~ e₂` iff joined by a walk internally
disjoint from `H` whose first and last edges are `e₁`, `e₂`.  `Relation.EqvGen` takes the
reflexive-transitive-symmetric closure (discharging "`~` is an equivalence relation").

**Book definition** (B&M §9.4, verbatim).  *Let `H` be a given subgraph of a graph
`G`.  We define a relation `∼` on `E(G) \ E(H)` by the condition that `e₁ ∼ e₂` if
there exists a walk `W` such that (i) the first and last edges of `W` are `e₁` and
`e₂`, respectively, and (ii) `W` is internally-disjoint from `H`.  It is easy to
verify that `∼` is an equivalence relation on `E(G) \ E(H)`.*

**Reading.**  Two edges outside `H` are related when you can travel from one to the
other without passing through `H`.  Grouping edges into classes carves
`G - E(H)` into the pieces that hang off `H` — those pieces are the bridges.

**Formalisation.**  `Relation.EqvGen` wraps the book's raw condition in its
reflexive–symmetric–transitive closure, which *discharges* the book's "it is easy
to verify" rather than proving it: whatever the raw relation does, the closure is
an equivalence by construction.  This is a deliberate trade — the file gains an
equivalence for free, at the cost that `bridgeRel` is a priori coarser than `∼`.
It is not actually coarser (the book's `∼` really is an equivalence), but nothing
here proves that, so do not appeal to "`bridgeRel e f` gives a single connecting
walk" — it gives a *chain* of them.  Several skeletons below rely on this
distinction. -/
def bridgeRel {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) :
    Sym2 V → Sym2 V → Prop :=
  Relation.EqvGen fun e₁ e₂ =>
    e₁ ∈ G.edgeSet \ H.edgeSet ∧ e₂ ∈ G.edgeSet \ H.edgeSet ∧
    ∃ (u v : V) (p : G.Walk u v), p.InternallyDisjointFrom H ∧
      p.edges.head? = some e₁ ∧ p.edges.getLast? = some e₂

/-- The **bridge** of `H` in `G` containing the edge `e`: the subgraph induced by `e`'s
`~`-class.  Built with `Subgraph.mk` directly — do NOT use `SimpleGraph.toSubgraph`
(`Subgraph.lean:559`), which is *spanning*.

**Book definition** (B&M §9.4, verbatim).  *A subgraph of `G - E(H)` induced by an
equivalence class under the relation `∼` is called a bridge of `H` in `G`.  It
follows immediately from the definition that if `B` is a bridge of `H`, then `B` is
a connected graph and, moreover, that any two vertices of `B` are connected by a
path that is internally-disjoint from `H`.  It is also easy to see that two bridges
of `H` have no vertices in common except, possibly, for vertices of `H`.*

The section then narrows: *In this section we are concerned with the study of
bridges of a cycle `C`.  Thus, to avoid repetition, we shall abbreviate "bridge of
`C`" to "bridge" in the coming discussion.*

**Reading.**  A bridge is one of the connected pieces remaining when `H` is
removed, together with the attachment points where it touches `H`.  The three
"immediate" facts quoted above are `bridgeOf_connected`,
`exists_path_internallyDisjoint` and `bridge_inter_subset_cycle` below — none of
them is actually immediate once `∼` is a closure.  In planar graph theory bridges
carry the argument: theorem 9.8 says inner bridges of a cycle avoid one another,
theorem 9.9 that a bridge avoiding every outer bridge is transferable, and together
these drive Kuratowski's theorem 9.10.

**Formalisation.**  Indexed by a *representative edge* `e` rather than by a class,
so "the bridge containing `e`"; two edges give the same bridge exactly when
`bridgeRel H e f`.  Built with `Subgraph.mk` directly — **not** with
`SimpleGraph.toSubgraph` (`Subgraph.lean:559`), which is *spanning* and would put
every vertex of `G` into every bridge.  Note `verts` is the union of the class's
edges, so it automatically includes the attachment points.

⚠ Because `bridgeRel` is reflexive for *any* `e` (it is an `EqvGen`), `bridgeOf H e`
is nonempty even for an `e` that is not an edge of `G` at all — it then has two
vertices and no edges.  Statements about bridges must therefore carry
`e ∈ G.edgeSet \ H.edgeSet` explicitly.  Two of them below originally omitted it and
were false as a result; both now carry it (see the module header). -/
def bridgeOf {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) (e : Sym2 V) :
    G.Subgraph where
  verts := {x | ∃ f, G.bridgeRel H e f ∧ x ∈ f}
  Adj u v := G.Adj u v ∧ G.bridgeRel H e s(u, v)
  adj_sub h := h.1
  edge_vert h := ⟨_, h.2, Sym2.mem_mk_left _ _⟩
  symm u v h := ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩

/-- Vertices of **attachment** of the bridge of `e` to the cycle traced by `c`:
`V(B) ∩ V(C)`.  (B&M's `V(B,H)`.)

**Book definition** (B&M §9.4, verbatim).  *For a bridge `B` of `H`, we write
`V(B) ∩ V(H) = V(B, H)`, and call the vertices in this set the vertices of
attachment of `B` to `H`.*

*In a connected graph every bridge has at least one vertex of attachment, and in a
block every bridge has at least two vertices of attachment.  A bridge with `k`
vertices of attachment is called a `k`-bridge.  Two `k`-bridges with the same
vertices of attachment are equivalent `k`-bridges.*

**Reading.**  The points at which the bridge touches down onto the cycle.  Almost
everything in §9.4 is a statement about how two bridges' attachment sets interleave
around `C` — `Overlaps`, `Skew` and the segments below are all built on this one
set.

**Formalisation.**  Specialised to `H = c.toSubgraph` for a closed walk `c`, since
§9.4 only ever needs bridges of a *cycle*.  A `Set V`, not a `Finset`, so that
`.ncard` is used for `k` (see theorem 9.6's conclusion).  "`B` is a `k`-bridge"
is spelled `(G.attach c e).ncard = k`, and "`B` and `B'` are equivalent" is
`G.attach c e = G.attach c e'`. -/
def attach {V : Type*} (G : SimpleGraph V) {u : V} (c : G.Walk u u) (e : Sym2 V) : Set V :=
  (G.bridgeOf c.toSubgraph e).verts ∩ c.toSubgraph.verts

/-- Position of a vertex along a cycle (index into its support).

**Book context** (B&M §9.4, §9.5).  The book has no such notion explicitly; it
speaks of vertices *appearing in the cyclic order `u, u', v, v'` on `C`*, and in
§9.5 introduces `C[u, v]` for the clockwise `(u,v)`-path along `C`.  This
definition is the bookkeeping that makes those phrases formal.

**Reading.**  Walking around the cycle from its base point, this records how many
steps it takes to reach `x`.  Comparing indices is how "cyclic order" is expressed
here.

**Formalisation.**  ⚠ Mathlib's `CircularOrder`/`Btw`/`SBtw` are order classes on a
*type* and do not apply to the support list of a particular cycle, so they are no
help.  ⚠ `List.idxOf` silently returns the list's `length` for an absent element,
so every use must be guarded by `x ∈ c.support` — unguarded, all missing vertices
quietly share one position past the end.  Note also that this is genuinely
*linear*, not cyclic: it is measured from `c`'s base point, so `InCyclicOrder`
below expresses a cyclic condition only up to the choice of that base point. -/
def Walk.cycleIdx {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (x : V) : ℕ := List.idxOf x c.support

/-- Four vertices in cyclic order on `c`.

**Book usage** (B&M §9.4, verbatim).  *…and the four vertices appear in the cyclic
order `u`, `u'`, `v`, `v'` on `C`.*

**Reading.**  Travelling once round the cycle, the four vertices are met in that
order.  This is the configuration making two bridges *skew*: each bridge's two
attachments separate the other's, so drawn inside the same region their connecting
paths would have to cross — which is precisely the Jordan-curve contradiction in
theorem 9.8.

**Formalisation.**  Rendered as a chain of strict `cycleIdx` inequalities, i.e. as
a *linear* order from `c`'s base point rather than a genuinely cyclic one.  This is
weaker than the book's phrase: the book's "cyclic order `u, u', v, v'`" is invariant
under rotation, whereas this version distinguishes rotations.  It suffices for
`Skew`, which existentially quantifies over which attachment plays which role and so
recovers rotation-invariance, but do not reuse `InCyclicOrder` where genuine
rotation-invariance is needed. -/
def Walk.InCyclicOrder {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (a b d e : V) : Prop :=
  c.cycleIdx a < c.cycleIdx b ∧ c.cycleIdx b < c.cycleIdx d ∧ c.cycleIdx d < c.cycleIdx e

/-- Forward distance along `c` from `a` to `x`, in steps, wrapping at the base point.

**Book context.**  B&M have no such notion; it is the arithmetic behind their
phrase *the segments of `B`* (§9.4) and behind `C[u, v]`, the clockwise
`(u,v)`-path of §9.5.

**Reading.**  Stand at `a` and walk forwards around the cycle; this counts the steps
until `x` is reached.  Unlike `cycleIdx` — which is measured from `c`'s own base
point and so is merely linear — this is genuinely cyclic: it is what lets an arc
"wrap round" past the base point.

**Formalisation.**  ⚠ Guard uses by `a, x ∈ c.support`.  `cycleIdx` returns
`c.support.length` for an absent vertex, which here yields a meaningless distance.
For `a` on the cycle the ℕ-subtraction never truncates: `cycleIdx a ≤ c.length`
(the base point occurs first at index `0`), so `cycleIdx x + c.length ≥ cycleIdx a`.
The `% c.length` is what performs the wraparound; for a degenerate `c` of length `0`
it is the identity (`n % 0 = n` in Lean), which is harmless since every use site
carries `hc : c.IsCycle`. -/
def Walk.cycleDist {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (a x : V) : ℕ :=
  (c.cycleIdx x + c.length - c.cycleIdx a) % c.length

/-- `x` lies on the closed arc of `c` running **forwards** from `a` to `b`.

**Book context** (B&M §9.4).  This is one of the *edge-disjoint paths* into which
the attachments of a bridge partition `C` — a **segment**, once `a` and `b` are
consecutive attachments (see `ConsecutiveAttach`).

**Reading.**  Walking forwards from `a`, you meet `x` no later than `b`.  Both
endpoints count as being on the arc, matching the book's segments, which share their
endpoints with the neighbouring segments and so are edge-disjoint but not
vertex-disjoint.

**Formalisation.**  Stated via `cycleDist`, so the wraparound is handled: the arc
from `a` to `b` may pass through `c`'s base point.  The `x ∈ c.support` conjunct is
the guard that keeps vertices off the cycle out, since `cycleDist` would otherwise
give them a spurious finite distance. -/
def Walk.OnArc {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (a b x : V) : Prop :=
  x ∈ c.support ∧ c.cycleDist a x ≤ c.cycleDist a b

/-- `a` and `b` are **consecutive** vertices of attachment of the bridge of `e`: both
are attachments, and no other attachment lies on the arc between them.

**Book context** (B&M §9.4, verbatim).  *The vertices of attachment of a `k`-bridge
`B` with `k ≥ 2` effect a partition of `C` into edge-disjoint paths, called the
segments of `B`.*

**Reading.**  The arc from `a` forwards to `b` is then exactly one **segment** of the
bridge — an arc of `C` with attachments at both ends and none in between.  Ranging
over all consecutive pairs recovers the book's partition of `C`.

**Formalisation.**  "No attachment strictly between" is phrased as: every attachment
on the closed arc is one of the two endpoints.  This is what makes the segments
partition `C` rather than merely cover it.  The definition does not require the
bridge to have `k ≥ 2` attachments; with fewer, no pair satisfies it, and `Avoids`
below is then false for want of a witness — which is the right answer, since a
`0`- or `1`-bridge has no segments to contain anything. -/
def ConsecutiveAttach {V : Type*} [DecidableEq V] (G : SimpleGraph V) {u : V}
    (c : G.Walk u u) (e : Sym2 V) (a b : V) : Prop :=
  a ∈ G.attach c e ∧ b ∈ G.attach c e ∧ a ≠ b ∧
    ∀ x ∈ G.attach c e, c.OnArc a b x → x = a ∨ x = b

/-- Two bridges of a cycle **avoid** one another: all the attachments of one lie in a
single segment of the other.

**Book definition** (B&M §9.4, verbatim).  *Two bridges avoid one another if all the
vertices of attachment of one bridge lie in a single segment of the other bridge;
otherwise they overlap.*

**Reading.**  Cut the cycle at one bridge's attachment points, producing arcs; the
two bridges avoid each other when the second's attachments all fall inside a single
arc, so both can be drawn on the same side of `C` without crossing.

**Formalisation.**  The disjunction mirrors the book's "of one bridge … of the
other", which is not symmetric on its face — the definition says only that *some*
assignment of the two roles works.  A segment of the bridge of `e` is the arc
`OnArc a b` for `a`, `b` consecutive attachments of `e`. -/
def Avoids {V : Type*} [DecidableEq V] (G : SimpleGraph V) {u : V}
    (c : G.Walk u u) (e e' : Sym2 V) : Prop :=
  (∃ a b, G.ConsecutiveAttach c e a b ∧ ∀ x ∈ G.attach c e', c.OnArc a b x) ∨
  (∃ a b, G.ConsecutiveAttach c e' a b ∧ ∀ x ∈ G.attach c e, c.OnArc a b x)

/-- Two bridges of a cycle **overlap**: they do not avoid one another.

**Book definition** (B&M §9.4, verbatim).  *Two bridges avoid one another if all the
vertices of attachment of one bridge lie in a single segment of the other bridge;
otherwise they overlap.*

**Reading.**  Neither bridge's attachments fit inside a single segment of the other,
so drawn on the same side of `C` they would be forced to cross.  Theorem 9.8 says
this cannot happen for two inner (or two outer) bridges of a plane graph, and
theorem 9.6 says overlapping comes in only two shapes.

**⚠ Repaired — previously `sorry`.**  This definition formerly had the body
`Prop := sorry`, making it an *opaque, unspecified* proposition and rendering
`overlap_imp_skew_or_equivalent_three_bridge` (theorem 9.6) vacuous: with `Overlaps`
opaque, that theorem said nothing about bridges and "proving" it would have
established nothing.  It also violated the project convention
(`.claude/CLAUDE.md`): *never `sorry` in a `def`* — a `sorry`-ed proof is an honest
debt, a `sorry`-ed definition is a silent change of meaning.

It is now the honest negation of `Avoids`, built on the segment machinery above
(`cycleDist` → `OnArc` → `ConsecutiveAttach` → `Avoids`), which is the layer B&M
assume when they speak of segments.  ⚠ `[DecidableEq V]` had to be added to the
signature, since `cycleIdx` needs it; every use site already had the instance. -/
def Overlaps {V : Type*} [DecidableEq V] (G : SimpleGraph V) {u : V}
    (c : G.Walk u u) (e e' : Sym2 V) : Prop := ¬ G.Avoids c e e'

/-- Two bridges of a cycle are **skew**: they have attachments `a, a', b, b'` occurring in
that cyclic order on `c` (`a, b` of one bridge, `a', b'` of the other).

**Book definition** (B&M §9.4, verbatim).  *Two bridges `B` and `B'` are skew if
there are four distinct vertices `u`, `v`, `u'` and `v'` of `C` such that `u` and
`v` are vertices of attachment of `B`, `u'` and `v'` are vertices of attachment of
`B'`, and the four vertices appear in the cyclic order `u`, `u'`, `v`, `v'` on
`C`.*

**Reading.**  The two bridges interleave around the cycle.  In a plane graph this is
fatal for two bridges on the same side: their connecting paths would have to cross,
contradicting the Jordan curve theorem — which is exactly the (dropped) proof of
theorem 9.8.

**Formalisation.**  The book asks for *four distinct* vertices; the Lean version
requires only `a ≠ b` and `a' ≠ b'`.  The remaining distinctness is implied by the
strict `cycleIdx` chain in `InCyclicOrder`, since distinct indices force distinct
vertices — provided all four lie on `c.support`, which the `attach` memberships
supply.  Rotation-invariance is recovered by the existential over which attachment
plays which role, compensating for `InCyclicOrder` being measured from `c`'s base
point. -/
def Skew {V : Type*} [DecidableEq V] (G : SimpleGraph V) {u : V}
    (c : G.Walk u u) (e e' : Sym2 V) : Prop :=
  ∃ a b a' b', a ≠ b ∧ a' ≠ b' ∧
    a ∈ G.attach c e ∧ b ∈ G.attach c e ∧
    a' ∈ G.attach c e' ∧ b' ∈ G.attach c e' ∧
    c.InCyclicOrder a a' b b'

/-- A **longest cycle**.

**Book usage** (B&M exercise 9.4.3(a), verbatim).  *Let `C = v₁v₂ … v_nv₁` be a
longest cycle in a nonhamiltonian connected graph `G`.*

**Reading.**  A cycle no shorter than any other cycle of `G`.  This is the standard
extremal device: assume the longest cycle is not a Hamilton cycle, then derive a
contradiction from the structure of the bridges hanging off it.  That is exactly how
Chvátal–Erdős is proved below.

**Formalisation.**  ⚠ Not `girth`/`egirth`, which are the *shortest* cycle — the
opposite extremum.  The maximality clause quantifies over cycles at *every* base
point `w`, not just at `u`, which is what makes it a genuine global maximum.  Note
the definition does not assert existence: `IsLongestCycle` is a hypothesis to be
supplied, and producing one requires knowing `G` has a cycle at all. -/
def Walk.IsLongestCycle {V : Type*} {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) : Prop :=
  c.IsCycle ∧ ∀ (w : V) (c' : G.Walk w w), c'.IsCycle → c'.length ≤ c.length

/-- The **Petersen graph**: the Kneser graph on 2-subsets of `Fin 5`.
⚠ MISSING from Mathlib (0 hits).  Honest def, real body.

**Book context.**  B&M never define the Petersen graph in the text; it is displayed
in Appendix III as the **`(3,5)`-cage** — the smallest 3-regular graph of girth 5 —
and referred to by name thereafter.  The description formalised here (2-element
subsets of a 5-set, adjacent when disjoint) is the standard Kneser presentation.

In chapter 9 it appears three times, all verbatim: exercise 9.3.1(b), *Using (a),
show that the Petersen graph is nonplanar*; exercise 9.5.2, *Show, using
Kuratowski's theorem, that the Petersen graph is non-planar*; and exercise
9.6.7(b), *Give an example of … a 3-regular 2-connected graph with no Tait
colouring*.  Chapter 6 adds exercise 6.1.2, *Show that the Petersen graph is
4-edge-chromatic* — which is what 9.6.7(b) needs.

**Reading.**  Ten vertices, 3-regular, girth 5, vertex- and edge-transitive, and a
counterexample to a remarkable number of plausible conjectures.  Here its role is
to show Tait's approach to the four-colour conjecture cannot be extended from
3-connected planar graphs to 2-connected ones.

**Formalisation.**  ⚠ Missing from Mathlib (0 hits), so defined here with a real
body.  Carrier `{s : Finset (Fin 5) // s.card = 2}`, adjacency `Disjoint`.
Looplessness needs the `card = 2` field: a set disjoint from itself is empty, which
contradicts having two elements.  3-regularity is then the count `C(3,2) = 3` of
2-subsets of the complementary 3-set — proved in exercise 9.6.7(b) below. -/
def petersenGraph : SimpleGraph {s : Finset (Fin 5) // s.card = 2} where
  Adj s t := Disjoint (s : Finset (Fin 5)) (t : Finset (Fin 5))
  symm := by intro s t h; exact h.symm
  loopless := by
    rintro ⟨s, hs⟩ h
    simp only [Finset.disjoint_self_iff_empty] at h
    simp [h] at hs

/-! ## Corollary 9.5.3 — RESTATED: the arithmetic core (`δ ≤ 5`)

⚠ NOT Cor 9.5.3.  Planarity is REPLACED by the `ε ≤ 3ν − 6` hypothesis (Cor 9.5.2,
dropped, would have supplied it).  Ship as `minDegree_le_five_of_card_edge_le`,
never `planar_minDegree_le_five`.  Stated additively to dodge truncated ℕ subtraction. -/

-- Cor 9.5.3 (arithmetic core): `ε + 6 ≤ 3ν` and `3 ≤ ν` ⇒ `δ ≤ 5`.
/-- **Corollary 9.5.3**, arithmetic core.  *If `G` is a simple planar graph, then
`δ ≤ 5`.*

**Book proof** (B&M §9.3, verbatim).  *This is trivial for `ν = 1, 2`.  If `ν ≥ 3`,
then, by theorem 1.1 and corollary 9.5.2,*

    δν ≤ ∑_{v ∈ V} d(v) = 2ε ≤ 6ν - 12

*It follows that `δ ≤ 5`.*

**Skeleton** (for `G.minDegree ≤ 5`, given `hν` and `hε`).
1. `by_contra`, `push_neg`: assume `6 ≤ G.minDegree`.
2. `G.minDegree ≤ G.degree v` for every `v` (`minDegree_le_degree`), so summing,
   `6 * ν ≤ ∑ v, G.degree v`.
3. Handshake (theorem 1.1): `∑ v, G.degree v = 2 * ε`
   (`sum_degrees_eq_twice_card_edges`).  With step 2, `6ν ≤ 2ε`.
4. `hε : ε + 6 ≤ 3ν` doubles to `2ε + 12 ≤ 6ν`.  Chaining with step 3 gives
   `2ε + 12 ≤ 2ε`, i.e. `12 ≤ 0`.  `omega` closes it.

**Reading.**  A planar graph cannot be everywhere dense: Euler's formula caps its
edge count at `3ν - 6`, so the average degree is below `6` and some vertex has
degree at most `5`.  This is the fact driving the five-colour theorem 9.11 — every
planar graph has a vertex of degree at most five to induct on — and it is why the
arithmetic core was worth salvaging even though the planarity around it was not.

**Formalisation.**  ⚠ This is **not** corollary 9.5.3 as the book states it.
Planarity is replaced by the hypothesis `hε`, which corollary 9.5.2 (dropped, being
unstatable without faces) would have supplied.  Ship it under the name
`minDegree_le_five_of_card_edge_le`, never as `planar_minDegree_le_five`: the
theorem proved is the arithmetic half only.  Stated additively (`ε + 6 ≤ 3ν`) to
dodge truncated ℕ-subtraction.

Worth knowing while filling: **`hν : 3 ≤ Fintype.card V` is unused.**  Steps 1–4
never mention `ν` except through the two inequalities `2ε + 12 ≤ 6ν` and
`6ν ≤ 2ε`, whose contradiction is independent of the size of `ν`.  The book needs
its `ν = 1, 2` caveat because it invokes corollary 9.5.2, which carries `ν ≥ 3`;
once that corollary is replaced by the raw hypothesis `hε`, the caveat evaporates.
`hν` is kept only so the statement still reads as the book's; do not go looking for
a place to use it. -/
theorem minDegree_le_five_of_card_edge_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hν : 3 ≤ Fintype.card V)
    (hε : G.edgeFinset.card + 6 ≤ 3 * Fintype.card V) :
    G.minDegree ≤ 5 := by
  sorry

/-! ## Exercise 9.3.3(a) — RESTATED: the arithmetic core (`G`, `Gᶜ` cannot both be sparse)

⚠ NOT Ex 9.3.3(a).  "Planar" is replaced by the Cor-9.5.2 edge bound on BOTH sides. -/

-- Ex 9.3.3(a) support lemma: `ε(G) + ε(Gᶜ) = C(ν, 2)`. ⚠ MISSING from Mathlib (0 hits).
/-- **Support lemma for exercise 9.3.3(a).**  `ε(G) + ε(Gᶜ) = C(ν, 2)`.

**Book proof.**  None — B&M do not state this separately; it is the arithmetic that
exercise 9.3.3(a) uses without comment.

**Skeleton** (for `G.edgeFinset.card + Gᶜ.edgeFinset.card = (card V).choose 2`).
1. **Disjointness.**  `G.edgeFinset` and `Gᶜ.edgeFinset` are disjoint: `Gᶜ.Adj u v`
   unfolds to `u ≠ v ∧ ¬ G.Adj u v`, so no `Sym2` lies in both.
2. **Union.**  Their union is `(⊤ : SimpleGraph V).edgeFinset` — every off-diagonal
   pair is an edge of exactly one of the two.  Prove by `Sym2.ind` and unfolding
   `compl_adj`.
3. **The count.**  `(⊤ : SimpleGraph V).edgeFinset.card = (card V).choose 2`; check
   for an existing Mathlib lemma first (`card_edgeFinset_top_eq_card_choose_two` or
   similar) before proving it.
4. `Finset.card_union_of_disjoint` on steps 1–2, then rewrite by step 3.

**Reading.**  Every unordered pair of distinct vertices carries an edge in exactly
one of `G` and `Gᶜ` — that is precisely what complementation means — so the two
edge counts partition the `C(ν, 2)` available pairs.  Together with the planar edge
bound applied to *both* graphs, this is the whole of exercise 9.3.3(a).

**Formalisation.**  ⚠ Missing from Mathlib (0 hits at the time of writing; step 3 is
the part most likely to exist already, so search before building).  Needs both
`DecidableRel G.Adj` and `DecidableRel Gᶜ.Adj` as instances, since `edgeFinset` is
only available with decidable adjacency. -/
theorem card_edgeFinset_add_card_edgeFinset_compl
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  sorry

-- Ex 9.3.3(a) (arithmetic core): for `ν ≥ 11`, `G` and `Gᶜ` cannot both satisfy `ε + 6 ≤ 3ν`.
/-- **Exercise 9.3.3(a)**, arithmetic core.  *If `G` is a simple planar graph with
`ν ≥ 11`, then `Gᶜ` is nonplanar.*

**Book proof.**  None — an exercise.

**Skeleton** (for `¬ (ε(G) + 6 ≤ 3ν ∧ ε(Gᶜ) + 6 ≤ 3ν)`, given `11 ≤ ν`).
1. `rintro ⟨h₁, h₂⟩` and add them: `ε(G) + ε(Gᶜ) + 12 ≤ 6ν`.
2. Rewrite by the support lemma: `(ν.choose 2) + 12 ≤ 6ν`.
3. **Clear the binomial without dividing.**  Multiply through by `2` and use
   `2 * ν.choose 2 = ν * (ν - 1)` (`Nat.choose_two_right` gives
   `ν.choose 2 = ν * (ν-1) / 2`; the doubled form avoids ℕ-division).  This yields
   `ν * (ν - 1) + 24 ≤ 12 * ν`.
4. **The arithmetic fails for `ν ≥ 11`.**  Substitute `ν = m + 11`:

       (m+11)(m+10) + 24 ≤ 12(m+11)
       m² + 21m + 134   ≤ 12m + 132
       m² + 9m + 2      ≤ 0

   which is false for every `m ≥ 0` — already at `m = 0`, where it reads `2 ≤ 0`.
   In practice: obtain `m` from `hν` by `Nat.exists_eq_add_of_le`, substitute, then
   `nlinarith`.  The margin is thin — at `ν = 11` the two sides of step 3 are `134`
   and `132` — so do not expect a slack-based tactic to find it unaided.

**Reading.**  Planarity forces sparsity, and a graph and its complement cannot both
be sparse: between them they must carry *every* possible edge, and `C(ν,2)` outgrows
`2(3ν-6)` at exactly `ν = 11`.  Part (b) of the exercise confirms the bound is
sharp in spirit — there is a simple planar graph on `ν = 8` vertices whose
complement is also planar.

**Formalisation.**  ⚠ This is **not** exercise 9.3.3(a) as stated.  "Planar" is
replaced by the corollary-9.5.2 edge bound on *both* sides, so what is proved is
that the two bounds are jointly unsatisfiable — the arithmetic obstruction, with
the topology stripped out.  The conclusion is therefore a negated conjunction
rather than "`Gᶜ` is nonplanar". -/
theorem not_both_card_edge_le_of_eleven_le
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    (hν : 11 ≤ Fintype.card V) :
    ¬ (G.edgeFinset.card + 6 ≤ 3 * Fintype.card V ∧
       Gᶜ.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  sorry

/-! ## Exercise 9.4.1: distinct bridges meet only on the cycle — bridge apparatus billed here -/

-- Ex 9.4.1: distinct bridges of `H` meet only in `V(H)`.
/-- **Exercise 9.4.1** (B&M §9.4, verbatim).  *Show that if `B` and `B'` are two
distinct bridges, then `V(B) ∩ V(B') ⊆ V(C)`.*

The text states it too: *It is also easy to see that two bridges of `H` have no
vertices in common except, possibly, for vertices of `H`.*

**Book proof.**  None — an exercise, and asserted as "easy to see" in the text.

**Skeleton** (for `(bridgeOf H e).verts ∩ (bridgeOf H e').verts ⊆ H.verts`).
1. `intro x hx`, `by_contra hxH`, so `x ∉ H.verts` and `x` lies in both bridges.
2. Unfold membership: `x ∈ (bridgeOf H e).verts` gives an edge `f` with
   `bridgeRel H e f` and `x ∈ f`; likewise `f'` with `bridgeRel H e' f'` and
   `x ∈ f'`.
3. **The connecting walk.**  Write `f = s(x, y)` and `f' = s(x, y')`.  The
   two-edge walk `y → x → y'` has `f` as first edge, `f'` as last edge, and its
   only internal vertex is `x`, which is not in `H.verts` by step 1.  So it
   witnesses the *generating* relation, giving `bridgeRel H f f'`.
   * Degenerate case to handle: if `f = f'` the conclusion is immediate; if
     `y = y'` the walk is still fine (it need not be a path).
4. Chain with `EqvGen`'s symmetry and transitivity:
   `bridgeRel H e f`, `bridgeRel H f f'`, `bridgeRel H f' e'` give
   `bridgeRel H e e'`, contradicting `hne`.

**Reading.**  Bridges can only meet on `H` itself.  If a vertex outside `H` lay in
two bridges, edges of both would meet there, and a walk through it from one to the
other stays outside `H` — so those edges are related and the two bridges were the
same class all along.  This is what makes the bridge decomposition genuinely a
decomposition: the bridges partition `E(G) \ E(H)` and meet only at attachment
points.

**Formalisation.**  "Distinct bridges" is `hne : ¬ G.bridgeRel H e e'` — two
representative edges in different classes — rather than a disequality of subgraphs,
which would be weaker and harder to use.  The hypotheses `he`, `he'` placing both
edges in `G.edgeSet \ H.edgeSet` are present and are needed: without them
`bridgeOf` degenerates (see its docstring). -/
theorem bridge_inter_subset_cycle
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (H : G.Subgraph)
    {e e' : Sym2 V} (he : e ∈ G.edgeSet \ H.edgeSet) (he' : e' ∈ G.edgeSet \ H.edgeSet)
    (hne : ¬ G.bridgeRel H e e') :
    (G.bridgeOf H e).verts ∩ (G.bridgeOf H e').verts ⊆ H.verts := by
  sorry

-- §9.4 hand-waved API (asserted "immediate" by B&M; really two lemmas). A bridge is connected.
/-- **Book assertion** (B&M §9.4, verbatim).  *It follows immediately from the
definition that if `B` is a bridge of `H`, then `B` is a connected graph…*

**Book proof.**  None — B&M call it immediate.  It is not: see the defect below and
the `bridgeRel` note about `EqvGen` chains.

**⚠ Statement repaired — hypothesis added.**  Without `e ∈ G.edgeSet \ H.edgeSet`
this theorem is **false**.  `bridgeRel` is an `EqvGen`, hence reflexive for *every*
`e : Sym2 V`, so for an `e` that is not an edge of `G` at all the class of `e` is
`{e}` and `bridgeOf H e` has `e`'s two endpoints as vertices and **no edges** —
disconnected whenever those endpoints differ.  Concretely: any `G`, any `H`, and
`e = s(a, b)` with `¬ G.Adj a b` and `a ≠ b`.  The hypothesis `he` has therefore
been **added**, matching `bridge_inter_subset_cycle` next door.  B&M do not state it
because their bridges are equivalence classes of genuine edges by construction; the
representative-edge encoding here is what makes it necessary.

**Skeleton** (for `((bridgeOf H e).coe).Connected`).
1. `Connected = Preconnected ∧ Nonempty`.  `Nonempty` holds because `he` puts both
   endpoints of `e` in `verts` (via reflexivity of `bridgeRel`).
2. For `Preconnected`, take `x, y ∈ verts`, so `x ∈ f` and `y ∈ g` for edges `f, g`
   with `bridgeRel H e f` and `bridgeRel H e g`, hence `bridgeRel H f g`.
3. **Induct on the `EqvGen` chain** from `f` to `g`.  This is the step the book's
   "immediately" hides: `bridgeRel` gives a *chain* of raw-relation steps, not one
   walk, so the connection must be assembled link by link.
   * *Base (raw step).*  A walk `W` internally disjoint from `H` with first edge
     `f` and last edge `g`.  Every edge of `W` is related to `f` (its initial
     segments are themselves internally disjoint from `H`), so `W` lies inside the
     bridge and connects an endpoint of `f` to an endpoint of `g` within it.
   * *Refl / symm / trans.*  Immediate, respectively by the empty walk, walk
     reversal, and concatenation.
4. Finally connect `x` to its `f`-endpoint and `y` to its `g`-endpoint — each is a
   single edge of the bridge, or nothing if they coincide.

**Reading.**  A bridge is one connected lump: its edges all lie in one `∼`-class,
and `∼` relates edges precisely when a walk avoiding `H`'s interior joins them.

**Formalisation.**  Together with `exists_path_internallyDisjoint` this is one of
two facts B&M wave through and that everything downstream (theorems 9.6, 9.7 and
exercise 9.4.3) actually consumes.  Step 3 is the real content and is worth
extracting as a lemma about `bridgeRel` chains, since the same induction is needed
for the companion result. -/
theorem bridgeOf_connected {V : Type*} (G : SimpleGraph V) (H : G.Subgraph) (e : Sym2 V)
    (he : e ∈ G.edgeSet \ H.edgeSet) :
    ((G.bridgeOf H e).coe).Connected := by
  sorry

-- §9.4 hand-waved API: any two vertices of a bridge are joined by an `H`-internally-disjoint path.
/-- **Book assertion** (B&M §9.4, verbatim).  *…and, moreover, that any two vertices
of `B` are connected by a path that is internally-disjoint from `H`.*

**Book proof.**  None — asserted as immediate, in the same breath as the previous
result.

**⚠ Statement repaired — hypothesis added.**  False without
`e ∈ G.edgeSet \ H.edgeSet`, for the same reason as `bridgeOf_connected`: taking
`e = s(a, b)` with `¬ G.Adj a b` puts `a` and `b` in `verts` while `G` may contain
no `(a,b)`-walk whatsoever, so no path can exist.  The hypothesis `he` has therefore
been **added**.

**Skeleton** (for `∀ u v ∈ (bridgeOf H e).verts, ∃ p : G.Walk u v, p.IsPath ∧ p.InternallyDisjointFrom H`).
1. Run the chain induction of `bridgeOf_connected` step 3, but carry the stronger
   invariant: the walk produced is internally disjoint from `H`, not merely that it
   exists.
   * *Base.*  The raw relation hands this over directly — its witness `W` is
     internally disjoint from `H` by definition.
   * *Trans.*  ⚠ **This is where care is needed.**  Concatenating two walks each
     internally disjoint from `H` need *not* give one internally disjoint from `H`:
     the join point becomes an internal vertex, and it may lie in `H.verts`.  The
     invariant survives only because the join point is an endpoint of an edge of the
     bridge, hence outside `H` unless it is an attachment — so strengthen the
     induction to track *which* endpoints are attachments, or route the
     concatenation through non-attachment vertices.
2. **Upgrade walk to path.**  `Walk.toPath` (`bypass`) extracts a path whose support
   is a sublist of the original's, so internal disjointness is inherited — state
   that as its own lemma, since `InternallyDisjointFrom` is about
   `support.tail.dropLast` and the sublist relation needs to be pushed through
   `tail`/`dropLast`.

**Reading.**  Not only is a bridge connected, but the connection can be made without
re-entering `H`.  This is the form actually used downstream: theorem 9.7 needs
`(v₁,v₂)`-paths inside a bridge avoiding the cycle internally, and the dropped
theorem 9.8 needs the same to reach its Jordan-curve contradiction.

**Formalisation.**  The path is asked for as a `G.Walk`, not a walk in the bridge.
That is equivalent and more convenient: a walk in `G` between two bridge vertices
that is internally disjoint from `H` automatically has all its edges in the bridge's
class.  Note the trans case in step 1 is the reason this is genuinely harder than
`bridgeOf_connected` and not a corollary of it. -/
theorem exists_path_internallyDisjoint {V : Type*} (G : SimpleGraph V) (H : G.Subgraph)
    (e : Sym2 V) (he : e ∈ G.edgeSet \ H.edgeSet) :
    ∀ u ∈ (G.bridgeOf H e).verts, ∀ v ∈ (G.bridgeOf H e).verts,
      ∃ p : G.Walk u v, p.IsPath ∧ p.InternallyDisjointFrom H := by
  sorry

/-! ## Theorem 9.7: a 3-attachment bridge contains a tripod -/

-- Thm 9.7: a bridge with 3 attachments `v₁,v₂,v₃` contains a tripod centred off `C`.
/-- **Theorem 9.7.**  *If a bridge `B` has three vertices of attachment `v₁`, `v₂`
and `v₃`, then there exists a vertex `v₀` in `V(B) \ V(C)` and three paths `P₁`,
`P₂`, `P₃` in `B` joining `v₀` to `v₁`, `v₂`, `v₃` respectively, such that for
`i ≠ j` the paths `Pᵢ` and `Pⱼ` have only the vertex `v₀` in common.*

**Book proof** (B&M §9.4, verbatim).  *Let `P` be a `(v₁, v₂)`-path in `B`,
internally-disjoint from `C`.  `P` must have an internal vertex `v`, since otherwise
the bridge `B` would be just `P`, and would not contain a third vertex `v₃`.  Let
`Q` be a `(v₃, v)`-path in `B`, internally-disjoint from `C`, and let `v₀` be the
first vertex of `Q` on `P`.  Denote by `P₁` the `(v₀, v₁)`-section of `P⁻¹`, by `P₂`
the `(v₀, v₂)`-section of `P`, and by `P₃` the `(v₀, v₃)`-section of `Q⁻¹`.  Clearly
`P₁`, `P₂` and `P₃` satisfy the required conditions.*

**Skeleton.**  Follows the book, with the two hand-waved steps made explicit.
1. `exists_path_internallyDisjoint` (with its `he` repair) gives a `(v₁, v₂)`-path
   `P` internally disjoint from `C`.
2. **`P` has an internal vertex.**  The book's "otherwise `B` would be just `P`":
   if `P` has none it is the single edge `v₁v₂`, so the class of `e` is `{s(v₁,v₂)}`
   and `(bridgeOf …).verts = {v₁, v₂}` — contradicting `v₃ ∈ verts` together with
   `h₁₃`, `h₂₃`.  Name the internal vertex `v`.
3. `exists_path_internallyDisjoint` again gives a `(v₃, v)`-path `Q` internally
   disjoint from `C`.
4. **`v₀` := the first vertex of `Q` on `P`.**  Exists because `v` is on both.
   Formalise with `Walk.takeUntil` against the predicate "lies in `P.support`", or
   by well-founded search along `Q.support`; the property to extract is that `v₀` is
   on `P`, and no *earlier* vertex of `Q` is.
5. **`v₀ ∉ C`** — the conclusion's `\ c.toSubgraph.verts`, and not stated by the
   book.  Argument: `Q` runs from `v₃ ∈ C` to `v ∉ C` and is internally disjoint
   from `C`, so `Q.support ∩ C = {v₃}`.  Since `v₃ ∉ P.support` (as `P` joins `v₁`
   to `v₂` and is internally disjoint from `C`, its only `C`-vertices are `v₁, v₂`,
   both `≠ v₃`), `v₀ ≠ v₃`, so `v₀` is an internal vertex of `Q` and hence off `C`.
6. **The three legs.**  `P₁ := (P.reverse).takeUntil v₀` reversed appropriately to
   run `v₀ → v₁`; `P₂ := P.dropUntil v₀`; `P₃ := (Q.takeUntil v₀).reverse`.  Mathlib:
   `Walk.takeUntil` / `Walk.dropUntil`, plus `IsPath.takeUntil` / `IsPath.dropUntil`
   for the `IsPath` conjuncts.
7. **Pairwise intersections are `{v₀}`.**  `P₁` and `P₂` are the two halves of the
   path `P` split at `v₀`, so `take_spec` plus `P.IsPath` gives support intersection
   `{v₀}`.  `P₃` meets `P` only at `v₀` by the minimality in step 4.

**Reading.**  The picture is a **tripod**: a hub `v₀` strictly off the cycle, with
three legs reaching down to the three attachment points.  This is what the dropped
theorem 9.8 uses to dispose of equivalent 3-bridges, and what Kuratowski's theorem
9.10 uses to locate `K_{3,3}` subdivisions.

**Formalisation.**  The "only the vertex `v₀` in common" conditions are spelled as
three `∀ x, x ∈ _.support → x ∈ _.support → x = v₀` clauses rather than as set
equalities, which is what the `takeUntil`/`dropUntil` lemmas deliver directly.
Note step 5 is genuinely extra work: the book states `v₀ ∈ V(B) \ V(C)` in the
theorem but never justifies it in the proof. -/
theorem bridge_tripod_of_three_attachments
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {u : V} {c : G.Walk u u} (hc : c.IsCycle) (e : Sym2 V)
    (he : e ∈ G.edgeSet \ c.toSubgraph.edgeSet)
    {v₁ v₂ v₃ : V} (h₁₂ : v₁ ≠ v₂) (h₁₃ : v₁ ≠ v₃) (h₂₃ : v₂ ≠ v₃)
    (ha : ∀ i ∈ ({v₁, v₂, v₃} : Set V),
      i ∈ (G.bridgeOf c.toSubgraph e).verts ∩ c.toSubgraph.verts) :
    ∃ (v₀ : V), v₀ ∈ (G.bridgeOf c.toSubgraph e).verts \ c.toSubgraph.verts ∧
      ∃ (P₁ : G.Walk v₀ v₁) (P₂ : G.Walk v₀ v₂) (P₃ : G.Walk v₀ v₃),
        P₁.IsPath ∧ P₂.IsPath ∧ P₃.IsPath ∧
        (∀ x, x ∈ P₁.support → x ∈ P₂.support → x = v₀) ∧
        (∀ x, x ∈ P₁.support → x ∈ P₃.support → x = v₀) ∧
        (∀ x, x ∈ P₂.support → x ∈ P₃.support → x = v₀) := by
  sorry

/-! ## Theorem 9.6: overlapping bridges are skew or equivalent 3-bridges -/

-- Thm 9.6: two overlapping bridges are skew, or equivalent 3-bridges.
/-- **Theorem 9.6.**  *If two bridges overlap, then either they are skew or else
they are equivalent 3-bridges.*

**Book proof** (B&M §9.4, verbatim).  *Suppose that the bridges `B` and `B'`
overlap.  Clearly, each must have at least two vertices of attachment.  Now if
either `B` or `B'` is a 2-bridge, it is easily verified that they must be skew.  We
may therefore assume that both `B` and `B'` have at least three vertices of
attachment.  There are two cases.*

*Case 1  `B` and `B'` are not equivalent bridges.  Then `B'` has a vertex of
attachment `u'` between two consecutive vertices of attachment `u` and `v` of `B`.
Since `B` and `B'` overlap, some vertex of attachment `v'` of `B'` does not lie in
the segment of `B` connecting `u` and `v`.  It now follows that `B` and `B'` are
skew.*

*Case 2  `B` and `B'` are equivalent `k`-bridges, `k ≥ 3`.  If `k ≥ 4`, then `B` and
`B'` are clearly skew; if `k = 3`, they are equivalent 3-bridges.*

**⚠ Previously vacuous — now stated.**  Until `Overlaps` was given an honest body
this theorem's hypothesis `hov : G.Overlaps c e e'` referred to an opaque
proposition, so the statement said nothing about bridges and "proving" it would have
established nothing.  `Overlaps` is now `¬ Avoids`, built on
`cycleDist`/`OnArc`/`ConsecutiveAttach`, so the theorem below is the book's.  The
skeleton is written against that repaired definition; unfolding `hov` gives
`¬ (∃ consecutive attachments … ) ∧ ¬ (∃ …)` after `push_neg`, which is the form
steps 1–4 consume.

**Skeleton** (for `Skew ∨ (attach c e = attach c e' ∧ (attach c e).ncard = 3)`).
1. **Each bridge has `≥ 2` attachments.**  From `hov`: a bridge with `≤ 1`
   attachment vacuously has all of them inside any single segment of the other, so
   it would avoid rather than overlap.  This is the book's "clearly".
2. **The 2-bridge case.**  If `(attach c e).ncard = 2`, say attachments `u, v`, they
   split `C` into exactly two segments.  Overlapping means `B'` has attachments in
   both open arcs; those two together with `u, v` interleave, giving `Skew`.
   Symmetrically if `B'` is the 2-bridge.  ("Easily verified" in the book; it is a
   short but real argument about arcs.)
3. **Case 1 — not equivalent.**  Some attachment `u'` of `B'` lies strictly between
   consecutive attachments `u, v` of `B`.  Overlap supplies an attachment `v'` of
   `B'` outside the segment `[u,v]`.  Then `u, u', v, v'` interleave: produce the
   `cycleIdx` chain and conclude `Skew`.
4. **Case 2 — equivalent `k`-bridges, `k ≥ 3`.**  If `k ≥ 4`, pick four attachments
   and interleave them (two for each bridge, alternating) to get `Skew`.  If
   `k = 3`, that is the right-hand disjunct: `attach c e = attach c e'` and
   `ncard = 3`.

**Reading.**  Overlapping comes in exactly two flavours.  This dichotomy is what the
dropped theorem 9.8 disposes of — the skew case by the Jordan curve theorem, the
equivalent-3-bridge case by the tripod of theorem 9.7.  It is the reason theorem 9.7
exists at all.

**Formalisation.**  "Equivalent 3-bridges" is rendered as the conjunction
`attach c e = attach c e' ∧ (attach c e).ncard = 3`, matching the book's definition
of equivalent `k`-bridges.  Steps 2–4 all reduce to arc arithmetic on `cycleIdx`,
so the segment machinery built for `Overlaps` will carry most of them. -/
theorem overlap_imp_skew_or_equivalent_three_bridge
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {u : V} {c : G.Walk u u} (hc : c.IsCycle) {e e' : Sym2 V}
    (hB : e ∈ G.edgeSet \ c.toSubgraph.edgeSet) (hB' : e' ∈ G.edgeSet \ c.toSubgraph.edgeSet)
    (hov : G.Overlaps c e e') :
    G.Skew c e e' ∨
      (G.attach c e = G.attach c e' ∧ (G.attach c e).ncard = 3) := by
  sorry

/-! ## Exercise 9.4.3(a): bridges of a longest cycle -/

-- Ex 9.4.3(a)(i): a nonhamiltonian connected graph has a bridge reaching off its longest cycle.
/-- **Exercise 9.4.3(a)(i)** (B&M §9.4, verbatim).  *Let `C = v₁v₂ … v_nv₁` be a
longest cycle in a nonhamiltonian connected graph `G`.  Show that (i) there exists a
bridge `B` such that `V(B) \ V(C) ≠ ∅`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `∃ e ∈ G.edgeSet \ c.toSubgraph.edgeSet, ((bridgeOf …).verts \ c.toSubgraph.verts).Nonempty`).
1. **`c` misses a vertex.**  `hnh : ¬ G.IsHamiltonian` and `hc.1 : c.IsCycle` give a
   `w ∉ c.support`: were `c` to meet every vertex it would be a Hamilton cycle.
   (Take care with the degenerate readings — `IsHamiltonian` is about the existence
   of *some* Hamilton cycle, so what is used is that `c` in particular is not one,
   which follows since otherwise `hnh` is contradicted outright.)
2. **A path from `w` to the cycle.**  `hconn` gives a walk from `w` to `c`'s base
   point; take one of *minimum length* among walks from `w` to any vertex of
   `c.support`.
3. **Minimality buys internal disjointness.**  By the choice in step 2, only the
   walk's final vertex lies on `c`; so the walk is internally disjoint from
   `c.toSubgraph`, and none of its edges is a cycle edge.
4. Let `e` be the walk's **first** edge (it has one: `w` is off the cycle, so the
   walk is nonempty).  Then `e ∈ G.edgeSet \ c.toSubgraph.edgeSet`, and step 3 makes
   the whole walk a witness to `bridgeRel`, putting every one of its vertices — `w`
   included — in `bridgeOf c.toSubgraph e`.
5. So `w ∈ verts \ c.toSubgraph.verts`, which is the required nonemptiness.

**Reading.**  Since `G` is not hamiltonian the longest cycle misses some vertex;
connectivity joins that vertex to the cycle, and the joining path's edges lie in a
bridge that therefore reaches off `C`.  This is the setup for the whole exercise —
that bridge is the object whose attachments part (ii) constrains, and Chvátal–Erdős
falls out of those constraints.

**Formalisation.**  Note this is the *only* one of the three 9.4.3 statements that
carries `hnh`; part (ii) as stated below drops it, which is where its defect comes
from. -/
theorem exists_bridge_off_longest_cycle
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hconn : G.Connected)
    (hnh : ¬ G.IsHamiltonian) {u : V} {c : G.Walk u u} (hc : c.IsLongestCycle) :
    ∃ e ∈ G.edgeSet \ c.toSubgraph.edgeSet,
      ((G.bridgeOf c.toSubgraph e).verts \ c.toSubgraph.verts).Nonempty := by
  sorry

-- Ex 9.4.3(a)(ii): if `vᵢ, vⱼ` are attachments of a bridge, then `vᵢ₊₁vⱼ₊₁ ∉ E`.
/-- **Exercise 9.4.3(a)(ii)** (B&M §9.4, verbatim).  *…(ii) if `vᵢ` and `vⱼ` are
vertices of attachment of `B`, then `v_{i+1}v_{j+1} ∉ E`.*

**Book proof.**  None — an exercise.

**⚠ Statement repaired — hypothesis added.**  Without `hoff` this is **false**.  In
the book, `B` is *the bridge produced by part (i)* — the one with a vertex off `C` —
but a naive transcription quantifies over an arbitrary bridge `e` and drops that
condition (and `¬ G.IsHamiltonian` with it).

*Counterexample.*  `G = K₅`, `c` the 5-cycle `v₁v₂v₃v₄v₅v₁`, which is a longest
cycle since `ν = 5`.  Every chord is its own bridge: a walk relating two distinct
chords would need an internal vertex, and every vertex lies on `C`, so no such walk
is internally disjoint from `C`.  Take `e = s(v₁, v₃)`, a 2-bridge with attachments
`v₁, v₃`.  Then `v_{i+1} = v₂` and `v_{j+1} = v₄`, and `G.Adj v₂ v₄` holds in `K₅` —
contradicting the conclusion, with every hypothesis satisfied.

`hoff` — exactly the conclusion of part (i) — has therefore been **added**.  It is
what makes the rerouting in step 3 below produce a *strictly* longer cycle rather
than one of the same length, which is precisely what the `K₅` example defeats.

**Skeleton** (for `¬ G.Adj (c.getVert (i+1)) (c.getVert (j+1))`).
1. `intro hadj`.
2. **A bridge path through a vertex off `C`.**  From `hi`, `hj` and `hoff`, use
   `exists_path_internallyDisjoint` to get a `(vᵢ, vⱼ)`-path `P` in the bridge,
   internally disjoint from `C` and with **at least one internal vertex** — this is
   where `hoff` is spent.
3. **Reroute.**  Build the closed walk

       vᵢ —P→ vⱼ —(C backwards)→ v_{i+1} —hadj→ v_{j+1} —(C forwards)→ vᵢ

   The two `C`-arcs between them cover every vertex of `C`: backwards from `vⱼ` to
   `v_{i+1}` sweeps `v_{i+1} … vⱼ`, and forwards from `v_{j+1}` to `vᵢ` sweeps
   `v_{j+1} … v_n, v_1 … vᵢ`.
4. **It is a cycle, and longer.**  It visits every vertex of `C` plus the internal
   vertices of `P` (which are off `C`, so new), so its length exceeds `c.length` by
   at least one.
5. Contradicts `hc.2` applied to this cycle.

**Reading.**  The successors of a bridge's attachment points form an *independent
set*.  That is exactly the leverage Chvátal–Erdős needs: a bridge with many
attachments yields a large independent set, which `α ≤ κ` forbids.

**Formalisation.**  Indices are into the walk (`c.getVert i`), so `i + 1` is the
successor along `c`; the wraparound at the end of the support is handled by
`getVert` saturating, which is why step 3 must be phrased as two explicit arcs
rather than as index arithmetic mod `n`. -/
theorem succ_attachments_not_adj
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hconn : G.Connected)
    {u : V} {c : G.Walk u u} (hc : c.IsLongestCycle) {e : Sym2 V}
    (he : e ∈ G.edgeSet \ c.toSubgraph.edgeSet)
    (hoff : ((G.bridgeOf c.toSubgraph e).verts \ c.toSubgraph.verts).Nonempty) {i j : ℕ}
    (hi : c.getVert i ∈ G.attach c e) (hj : c.getVert j ∈ G.attach c e)
    (hij : c.getVert i ≠ c.getVert j) :
    ¬ G.Adj (c.getVert (i + 1)) (c.getVert (j + 1)) := by
  sorry

/-! ## Exercise 9.4.3(b): Chvátal–Erdős — `α ≤ κ ⇒` hamiltonian -/

-- Ex 9.4.3(b) (Chvátal–Erdős): `3 ≤ ν`, connected, `α ≤ κ` ⇒ `G` hamiltonian.
-- ⚠ `3 ≤ ν` is LOAD-BEARING (B&M omit it; false without it — see K₂).
/-- **Exercise 9.4.3(b)** (Chvátal and Erdős).  *Deduce that if `α ≤ κ`, then `G`
is hamiltonian.*

**Book proof.**  None — an exercise; "deduce" points at part (a).

**Skeleton** (for `G.IsHamiltonian`).
1. `by_contra hnh`.  Dispose of the degenerate case first: if `α = 1` then `G` is
   complete, and a complete graph on `ν ≥ 3` vertices is hamiltonian.  So `α ≥ 2`,
   hence `κ ≥ 2` by `h`, hence `G` is 2-connected and in particular has a cycle.
2. **A longest cycle exists.**  Cycles have length `≤ ν` and there is at least one
   (step 1), so a maximum is attained; call it `c`, giving `hc : c.IsLongestCycle`.
3. **The bridge.**  Part (a)(i) supplies `e` whose bridge `B` has a vertex `w` off
   `c`.  Let `A := G.attach c e` be its attachments and `k := A.ncard`.
4. **`κ ≤ k`.**  `A` is a vertex cut: deleting it disconnects `w` from the rest of
   `c` — any path out of `B` must pass through an attachment.  (Needs `c` to retain
   vertices outside `A`, which holds since a longest cycle in a 2-connected
   non-hamiltonian graph is longer than its own bridge's attachment set; establish
   this explicitly.)  Then `vertexConnectivity ≤ A.card` by the `sInf` bound.
5. **An independent set of size `k + 1`.**  By (a)(ii) — with its `hoff` repair,
   available here because step 3 supplies exactly that hypothesis — the successors
   `{c.getVert (i+1) : c.getVert i ∈ A}` are pairwise non-adjacent, giving `k`
   independent vertices.  Adjoin `w`: no successor is adjacent to `w`, since such an
   edge would make that successor an attachment of `B` and yield a longer cycle by
   the rerouting of (a)(ii) step 3.
6. So `κ + 1 ≤ k + 1 ≤ α`, contradicting `h : α ≤ κ`.

**Reading.**  `α` is the independence number and `κ` the connectivity, so the
hypothesis says the graph is at least as well connected as it is "spread out".  This
is one of the most elegant sufficient conditions for hamiltonicity known, and the
whole bridge apparatus of §9.4 that survives in this file exists to reach it — it is
the prize of the surviving combinatorial core.

**Formalisation.**  ⚠ `hν : 3 ≤ Fintype.card V` is **load-bearing** and is *not* in
B&M — the statement is false without it.  `K₂` has `α = 1` and `κ = 1`, so `α ≤ κ`
holds, yet `K₂` has no Hamilton cycle, there being no cycle of length two.  (`K₁` is
similar.)  Step 5 is where most of the work sits; step 4's cut argument is the part
most likely to need its own supporting lemma. -/
theorem chvatal_erdos_hamiltonian
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hν : 3 ≤ Fintype.card V)
    (hconn : G.Connected)
    (h : G.indepNum ≤ G.vertexConnectivity) :
    G.IsHamiltonian := by
  sorry

/-! ## Exercise 9.6.4: every hamiltonian 3-regular graph has a Tait colouring

A *Tait colouring* is a proper 3-edge-colouring of a 3-regular graph, expressed exactly
as `G.lineGraph.Colorable 3` (no new definitions). -/

-- Ex 9.6.4: hamiltonian 3-regular ⇒ Tait colouring (`lineGraph.Colorable 3`).
/-- **Exercise 9.6.4** (B&M §9.6, verbatim).  *Show that every hamiltonian 3-regular
graph has a Tait colouring.*

The term is §9.6: *A proper 3-edge colouring of a 3-regular graph is often called a
Tait colouring.*

**Book proof.**  None — an exercise.

**Skeleton** (for `G.lineGraph.Colorable 3`).
1. **`ν` is even.**  Handshake with 3-regularity: `3ν = ∑ v, d(v) = 2ε`, so `2 ∣ 3ν`
   and hence `2 ∣ ν`.  This is what makes step 3 well defined.
2. **The complement of the cycle is a perfect matching.**  `hc` makes `c` a Hamilton
   cycle, so it meets every vertex and uses exactly two edges at each; 3-regularity
   leaves exactly one non-cycle edge at each vertex.  Define
   `M := G.edgeFinset \ c.edges`.
3. **The colouring.**  Edges of `M` get colour `2`.  An edge of `c` gets colour
   `0` or `1` according to the parity of its position along `c` — well defined as a
   proper 2-colouring of the cycle's edges exactly because `ν` is even (step 1).
4. **Properness in the line graph.**  Two `lineGraph`-adjacent edges share an end
   `v`.  The three edges at `v` are two consecutive cycle edges — consecutive
   positions, so opposite parities, so colours `0` and `1` — and one matching edge
   of colour `2`.  All three differ, so any two of them differ.
5. Package as a `G.lineGraph.Coloring (Fin 3)` and conclude `Colorable 3`.

**Reading.**  A cubic hamiltonian graph splits into an even cycle plus a perfect
matching; two colours alternate around the cycle and the third takes the matching.

*Why this matters (§9.7).*  Tait (1880) showed the four-colour conjecture equivalent
to "every simple 3-regular 3-connected planar graph has a Tait colouring" (theorem
9.12(iii)), and then *by mistakenly assuming that every such graph is hamiltonian*,
gave a "proof" of the conjecture using exactly this exercise.  Over half a century
later Tutte (1946) exhibited a nonhamiltonian 3-regular 3-connected planar graph,
invalidating the argument.  So this exercise is sound; only Tait's extra assumption
was not.

**Formalisation.**  A Tait colouring is spelled `G.lineGraph.Colorable 3`, needing
no new definitions — `lineGraph` has the edges of `G` as vertices, adjacent when
they share an end, so a proper colouring of it *is* a proper edge colouring of `G`.
Step 3's parity assignment is the fiddly part: it needs a function from an edge of
`c` to its index along `c`, which `c.edges` provides as a list position. -/
theorem lineGraph_colorable_three_of_isHamiltonian_of_three_regular
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3)
    {a : V} {c : G.Walk a a} (hc : c.IsHamiltonianCycle) :
    G.lineGraph.Colorable 3 := by
  sorry

/-! ## Exercise 9.6.7(b): a 3-regular 2-connected graph with no Tait colouring (Petersen) -/

/-! ### Book content for the dropped material

Mathlib has no plane topology, so the following are unstatable here.  They are
recorded for reference, since the surviving combinatorial core exists to serve
them; quotations are verbatim, as elsewhere in this file.

What would be needed to recover any of it: a notion of embedding in `ℝ²` (or a
combinatorial surrogate — a rotation system), the Jordan curve theorem, and from
those a definition of *face*.  Euler's formula, the dual, Kuratowski and the
colour theorems all follow from that layer and none is reachable without it.
Corollaries 9.5.2 and 9.5.3 are the exceptions whose *arithmetic* halves survive
above, precisely because their topology enters only through a single edge bound.

*Theorem 9.1 / exercise 9.1.1.*  `K₅` and `K_{3,3}` are nonplanar.  The proof of theorem
9.1 draws the triangle `v₁v₂v₃` as a Jordan curve, places `v₄` inside,
notes the edges from `v₄` split the interior into three regions, and shows `v₅`
cannot be placed in any of the four available regions without an edge crossing
the curve.

*Theorem 9.2.*  A graph is embeddable in the plane if and only if it is
embeddable on the sphere — via **stereographic projection** from a point `z` of
the sphere not on the embedded graph.

*Theorem 9.3.*  Any vertex of a planar graph can be put on the exterior face of
some embedding: embed on the sphere and project from a point inside a face
containing that vertex.

*Theorem 9.4.*  `∑_{f ∈ F} d(f) = 2ε` for a plane graph — the face analogue of the
handshaking theorem 1.1, proved by applying it to the dual.

*Theorem 9.5 (Euler's formula).*  `ν - ε + φ = 2` for a connected plane graph.  By
induction on `φ`: with `φ = 1` the graph is a tree and `ε = ν - 1`; otherwise
delete a non-cut edge, merging the two faces it separates.  Corollaries: all
embeddings of a connected planar graph have the same number of faces (9.5.1);
`ε ≤ 3ν - 6` for simple planar `G` with `ν ≥ 3` (9.5.2); `δ ≤ 5` (9.5.3); and
`K₅`, `K_{3,3}` are nonplanar (9.5.4, 9.5.5).

*Theorems 9.8 and 9.9.*  Inner (outer) bridges avoid one another — skew inner
bridges would force their connecting paths to cross, and equivalent inner
3-bridges would force a tripod leg to cross, both contradicting the Jordan curve
theorem.  An inner bridge avoiding every outer bridge is **transferable**: its
attachments all lie on one face outside `C`, so it can be redrawn there.

*Theorem 9.10 (Kuratowski, 1930).*  A graph is planar if and only if it contains
no subdivision of `K₅` or `K_{3,3}`.  The proof (Dirac and Schuster, 1954) takes a
minimal counterexample, shows it simple and 3-connected (lemmas 9.10.1–9.10.4),
embeds `G - uv`, chooses a cycle `C` through `u`, `v` with as many interior edges
as possible, and shows some inner bridge skew to `uv` overlaps an outer bridge —
then extracts a `K₅` or `K_{3,3}` subdivision in each of four cases.  Wagner
(1937) gave the contraction analogue.

*Theorem 9.11 (the five-colour theorem, Heawood 1890).*  Every planar graph is
5-vertex-colourable.  A 6-critical plane graph would have `δ = 5` by
corollary 9.5.3 and theorem 8.1; the Kempe-chain argument on the two-coloured
subgraphs `G_ij` around a degree-5 vertex then contradicts the Jordan curve
theorem.

*The four-colour conjecture and theorem 9.12.*  A **`k`-face colouring** assigns
colours to faces, proper when no two faces separated by an edge agree;
`χ*(G) = χ(G*)`.  Theorem 9.12: the following are equivalent — (i) every planar
graph is 4-vertex-colourable; (ii) every plane graph is 4-face-colourable;
(iii) every simple 2-edge-connected 3-regular planar graph is 3-edge-colourable.
Equivalence (ii) ⇒ (iii) colours each edge by the sum, over `GF(2)²`, of the two
face colours it separates.  Tait (1880) observed (iii); the conjecture was settled
affirmatively by Appel and Haken.

*Theorem 9.13 (Grinberg, 1968).*  For a loopless plane graph with a Hamilton cycle
`C`, `∑_{i} (i-2)(φ'ᵢ - φ''ᵢ) = 0`, where `φ'ᵢ` and `φ''ᵢ` count faces of degree
`i` inside and outside `C`.  This gives a quick nonhamiltonicity test — the
Grinberg graph has faces only of degrees 5, 8, 9, and the unique 9-face makes the
congruence `7(φ'₉ - φ''₉) ≡ 0 (mod 3)` impossible.

*Tutte's graph (§9.7).*  Tutte (1946) constructed a nonhamiltonian 3-regular
3-connected planar graph, refuting Tait's assumption.  Tutte (1956) later showed
every 4-connected planar graph is hamiltonian.

*§9.8, the planarity algorithm.*  Demoucron, Malgrange and Pertuiset (1964) grow
an increasing sequence of planar subgraphs `G₁ ⊆ G₂ ⊆ …` with embeddings, at each
step computing the bridges of `Gᵢ` and the set `F(B, G̃ᵢ)` of faces each bridge is
**drawable** in.  Theorem 9.14: if `G̃` is `G`-admissible then `F(B, G̃) ≠ ∅` for
every bridge — so an empty such set certifies nonplanarity.  The algorithm is
good; Hopcroft and Tarjan (1974) gave a faster one. -/

end SimpleGraph
