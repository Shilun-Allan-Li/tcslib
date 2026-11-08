import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Relation

/-!
# Bondy & Murty, *Graph Theory with Applications* — Chapter 11: Networks

Sorry-skeleton extracted from `papers/bondy-murty-ch11-networks.md`.

Every proof body is `sorry`; this file is a scaffold for sorry-driven development
(fill one stub at a time, `lake build` after each).

## Design notes (from the outline)

* **Mathlib has ZERO flow/network API** (0 hits for max-flow/min-cut/Menger/capacity), so the entire
  `Network`/`IsFlow`/`f⁺`/`f⁻`/`val`/cut theory is defined here from scratch.
* **Carrier**: capacity-as-a-function `cap : V → V → ℕ` (`cap u v = 0` ⟺ no arc). This makes `f⁺`/`f⁻`
  plain `Finset.sum`s.  ⚠ It cannot represent parallel arcs — a real restriction for Lemma 11.4.
* **`val` and every `f⁺ − f⁻` are ℤ-valued** — in ℕ the truncated subtraction makes Ex 11.1.2 false.
* The repo's `SimpleGraph.InternallyDisjoint`, `vertexConnectivity`, `edgeConnectivity`
  (in `TCSlib.GraphTheory.Connectivity`) are **deliberately not imported** here; minimal local copies
  are provided so this file stands alone (see the `-- NOTE:` markers).
* Directed-path counts (`maxArcDisjointDirectedPaths`, …) are genuinely MISSING from Mathlib and have
  no honest carrier without a directed-path API; they are stubbed `:= sorry` so the *statements*
  typecheck.  ⚠ **This justification is too broad — see the defect note below.**
* Dropped/omitted items are documented at the bottom of the file.

## How each declaration is annotated

Every docstring below has a fixed shape, so that the book's own mathematics stays
separable from this file's formalisation choices:

1. **The book's own statement** (for a theorem) or **definition** (for a `def`),
   quoted verbatim from Bondy & Murty, with the LaTeX transcribed into Lean-style
   backticks.
2. **Book proof** — B&M's printed proof, again verbatim.  Chapter 11 proves lemmas
   11.1 and 11.4, theorems 11.1–11.9 and corollaries 11.1, 11.5; everything else is
   an exercise or an assumed-silently step, and says so rather than being filled in
   with a reconstruction.
3. **Skeleton** — an *abstract* plan, numbered, keyed to the Lean statement as it
   actually appears here.  Each step names the intermediate fact and the
   Mathlib/local notion it is stated in; it deliberately does **not** commit to
   tactics.
4. **Reading** — informal intuition: what the result means and how it sits among
   the chapter's other results.
5. **Formalisation** — present only where the Lean statement departs from the
   book's, recording what was changed and why.

Definitions carry parts 1, 4 and 5 only: there is nothing to prove.

## ⚠ Fourteen definitions in this file have `sorry` bodies

This is the dominant problem with the file and it is worth stating plainly, since
the design notes above present the stubbing as a considered choice rather than as
a cost.  A `sorry`-ed *proof* is an honest debt; a `sorry`-ed *definition* is an
opaque constant, so every statement mentioning it is vacuous — it typechecks but
asserts nothing.  The affected declarations, and what they take down with them:

* **The twelve extremal path counts** (`maxArcDisjointDirectedPaths`,
  `minArcsDestroyingDirectedPaths`, `maxInternallyDisjointDirectedPaths`,
  `minVerticesDestroyingDirectedPaths`, `maxEdgeDisjointPaths`,
  `minEdgesDestroyingPaths`, `maxInternallyDisjointPaths`,
  `minVerticesDestroyingPaths`, `maxSTVertexDisjointPaths`, `minSTSeparator`,
  `Network.maxArcDisjointPaths`, `Network.minArcsDestroyingPaths`).  These are
  *both sides* of every Menger statement, so **the whole of §11.4 is currently
  vacuous**: lemma 11.4(a)(b), theorems 11.4–11.7, corollaries 11.5 and 11.7, and
  exercises 11.4.1 and 11.4.3 — ten statements, and the chapter's headline
  application.
* **`Network.IncPath.iota`** and **`Network.revisedFlow`**, which make exercise
  11.3.1 vacuous and hollow out the forward direction of theorem 11.2.

⚠ The design note's justification — *"no honest carrier without a directed-path
API"* — holds only for the six *directed* counts.  The six **undirected** ones
(`maxEdgeDisjointPaths`, `minEdgesDestroyingPaths`, `maxInternallyDisjointPaths`,
`minVerticesDestroyingPaths`, `maxSTVertexDisjointPaths`, `minSTSeparator`) are
definable today from what this file already imports: `SimpleGraph.Walk`,
`Walk.IsPath`, `Walk.edges`, `deleteEdges`, `induce` and the local
`InternallyDisjoint` suffice, with `sSup`/`sInf` over the obvious sets.  The
directed six need a directed-path notion, which `TCSlib/GraphTheory/DirectedGraphs.lean`
does supply (`Digraph.IsDirectedPath` over `Quiver.Path`) — though its
arc-disjointness rests on `arcsOf`, itself `sorry`-bodied there.  Per-declaration
repairs are given in the individual docstrings.
-/

namespace Networks

/-! ## The carrier: networks -/

/-- A **network** `N = (D, X, Y, c)`. ⚠ MISSING from Mathlib (0 hits).
`cap u v = 0` encodes "no arc `u → v`".  `X`/`Y` are the source/sink *sets* of §11.1; `x`/`y` are the
distinguished single source/sink used from §11.2 onward (cuts).

**Book definition** (B&M §11.1, verbatim).  *A network `N` is a digraph `D` (the
underlying digraph of `N`) with two distinguished subsets of vertices, `X` and `Y`,
and a non-negative integer-valued function `c` defined on its arc set `A`; the sets
`X` and `Y` are assumed to be disjoint and nonempty.  The vertices in `X` are the
sources of `N` and those in `Y` are the sinks of `N`.  They correspond to
production centres and markets, respectively.  …  The function `c` is the capacity
function of `N` and its value on an arc `a` the capacity of `a`.  The capacity of
an arc can be thought of as representing the maximum rate at which a commodity can
be transported along it.*

**Reading.**  A transportation network: goods are produced at the sources, consumed
at the sinks, and shipped along the arcs, each with a maximum throughput.

**Formalisation.**  ⚠ Missing from Mathlib (0 hits for flow/network/capacity).
Capacity is carried as a *function* `cap : V → V → ℕ`, with `cap u v = 0` encoding
"no arc `u → v`"; this makes `f⁺`/`f⁻` plain `Finset.sum`s.  ⚠ It cannot represent
**parallel arcs**, which is a real restriction — lemma 11.4 is about a network in
which every arc has unit capacity, and B&M's digraphs may have several arcs between
the same pair.

The structure carries **both** `X`, `Y` (the source/sink *sets* of §11.1) and the
distinguished `x`, `y` used from §11.2 onward.  That is because the book reduces
the first to the second: *adjoin two new vertices `x` and `y`; join `x` to each
vertex in `X` by an arc of capacity `∞`; join each vertex in `Y` to `y` by an arc
of capacity `∞`; designate `x` as the source and `y` as the sink of `N'`* — after
which *throughout the next three sections, we shall confine our attention to
networks that have a single source `x` and a single sink `y`*.  That reduction is
exercise 11.1.4, which is deferred here (it needs an `ℕ∞`-capacity parallel
carrier), so the two are simply both recorded in the structure.

**⚠ Structural defect: `x`, `y` are unrelated to `X`, `Y`.**  Nothing in the
structure requires `N.x ∈ N.X`, let alone `N.X = {N.x}`.  But `val` is defined over
the *set* `X` while every §11.2–§11.3 result is about cuts separating the single
`x` from the single `y`.  The two therefore measure different things, and **lemma
11.1, theorem 11.1 in both forms, corollary 11.1 and theorem 11.3 are all false as
stated**.

*Counterexample* (one network refutes all of them).  `V = {x₁, x₂, y₁}`,
`X = {x₁, x₂}`, `Y = {y₁}`, `N.x = x₁`, `N.y = y₁`; capacities `c(x₁,y₁) = c(x₂,y₁) = 1`
and `0` elsewhere.  Then `I = ∅`, so any `f` within capacity is a flow; take
`f(x₁,y₁) = f(x₂,y₁) = 1`.

* `val f = f⁺(X) - f⁻(X) = 2`.
* `S = {x₁}` is a cut (`x₁ ∈ S`, `y₁ ∉ S`), with `f⁺(S) - f⁻(S) = 1` and
  `cap S = 1`.
* So lemma 11.1 asserts `2 = 1`; theorem 11.1 asserts `2 ≤ 1`.
* Max flow value is `2`, minimum cut capacity is `1`, so theorem 11.3 asserts
  `2 = 1`.
* Corollary 11.1 fails too: `f'(x₁,y₁) = 1`, `f'(x₂,y₁) = 0` has
  `val f' = 1 = cap{x₁}`, yet `f'` is not a maximum flow.

*The repair* is to add the fields `hx : N.X = {N.x}` and `hy : N.Y = {N.y}` to the
structure (the book's standing convention for §§11.2–11.4), or equivalently to add
them as hypotheses on the affected theorems.  The §11.1 results — exercises 11.1.2
and 11.1.3 — are unaffected and should keep the general `X`, `Y`. -/
structure Network (V : Type*) where
  /-- Capacity of arc `u → v` (`0` ⟺ no arc). -/
  cap : V → V → ℕ
  /-- Source set. -/
  X : Finset V
  /-- Sink set. -/
  Y : Finset V
  /-- Distinguished single source (§11.2+). -/
  x : V
  /-- Distinguished single sink (§11.2+). -/
  y : V
  hdisj : Disjoint X Y
  hX : X.Nonempty
  hY : Y.Nonempty

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Key Definitions -/

/-- Intermediate vertices `I = V \ (X ∪ Y)`.

**Book definition** (B&M §11.1, verbatim).  *Vertices which are neither sources nor
sinks are called intermediate vertices; the set of such vertices will be denoted by
`I`.*

**Reading.**  The transit points of the network, which neither produce nor consume.
The conservation condition (11.2) applies exactly here — what flows in must flow
out — and that is what makes `val f` well defined (exercise 11.1.3).

**Formalisation.**  `Finset.univ \ (X ∪ Y)`, so `I` is a `Finset` and membership is
decidable — needed by `IsFlow`'s second clause. -/
def Network.I (N : Network V) : Finset V := Finset.univ \ (N.X ∪ N.Y)

/-- `f⁺(S) = f(S, S̄) = ∑_{u∈S} ∑_{v∉S} f u v`. ⚠ MISSING.

**Book notation** (B&M §11.1, verbatim).  *If `S ⊆ V`, we denote `V \ S` by `S̄`. …
If `f` is a real-valued function defined on the arc set `A` of `N`, and if
`K ⊆ A`, we denote `∑_{a ∈ K} f(a)` by `f(K)`.  Furthermore, if `K` is a set of
arcs of the form `(S, S̄)`, we shall write `f⁺(S)` for `f(S, S̄)` and `f⁻(S)` for
`f(S̄, S)`.*

**Reading.**  The total flow leaving `S` — sum over every arc with tail inside `S`
and head outside.  ⚠ This is *not* the sum of the `f⁺(v)` over `v ∈ S`: arcs
internal to `S` are counted there but not here.  Exercise 11.1.2 makes the exact
relationship precise, and it is the difference `f⁺ - f⁻` that behaves well.

**Formalisation.**  ⚠ Missing from Mathlib.  A double `Finset.sum` over `S` and
`Sᶜ`, which the capacity-as-a-function carrier makes possible; `f u v = 0` for a
non-arc contributes nothing. -/
def Network.fOut (_N : Network V) (f : V → V → ℕ) (S : Finset V) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, f u v

/-- `f⁻(S) = f(S̄, S) = ∑_{u∉S} ∑_{v∈S} f u v`. ⚠ MISSING.

**Book notation** (B&M §11.1, verbatim).  *…and `f⁻(S)` for `f(S̄, S)`.*

The book names the difference: *If `S` is a subset of vertices in a network `N` and
`f` is a flow in `N`, then `f⁺(S) - f⁻(S)` is called the resultant flow out of `S`,
and `f⁻(S) - f⁺(S)` the resultant flow into `S`, relative to `f`.*

**Reading.**  The total flow entering `S`.  Conservation forces the resultant flow
out of every intermediate vertex to vanish, which is what makes the resultant flow
out of `X` equal the resultant flow into `Y` (exercise 11.1.3) and hence `val f`
well defined.

**Formalisation.**  The mirror of `fOut` with the two sums swapped. -/
def Network.fIn (_N : Network V) (f : V → V → ℕ) (S : Finset V) : ℕ :=
  ∑ u ∈ Sᶜ, ∑ v ∈ S, f u v

/-- A **flow**: (11.1) capacity constraint + (11.2) conservation at intermediate vertices.

**Book definition** (B&M §11.1, verbatim).  *A flow in a network `N` is an
integer-valued function `f` defined on `A` such that*

    0 ≤ f(a) ≤ c(a)   for all a ∈ A                                  (11.1)
    f⁻(v) = f⁺(v)     for all v ∈ I                                  (11.2)

*The upper bound in condition (11.1) is called the capacity constraint; it imposes
the natural restriction that the rate of flow along an arc cannot exceed the
capacity of the arc.  Condition (11.2), called the conservation condition, requires
that, for any intermediate vertex `v`, the rate at which material is transported
into `v` is equal to the rate at which it is transported out of `v`.  Note that
every network has at least one flow, since the function `f` defined by `f(a) = 0`,
for all `a ∈ A`, clearly satisfies both (11.1) and (11.2); it is called the zero
flow.*

**Reading.**  Nothing over-loaded, nothing accumulating.  The zero flow's existence
is what makes `exists_maxFlow` non-vacuous.

**Formalisation.**  The lower bound `0 ≤ f(a)` of (11.1) is free: `f` is ℕ-valued.
Conservation is stated as `fIn f {v} = fOut f {v}` on singletons, which unfolds to
the book's `f⁻(v) = f⁺(v)` — note `fIn`/`fOut` on a singleton are genuinely the
per-vertex quantities, since there are no arcs internal to a singleton. -/
def Network.IsFlow (N : Network V) (f : V → V → ℕ) : Prop :=
  (∀ u v, f u v ≤ N.cap u v) ∧
  (∀ v ∈ N.I, N.fIn f {v} = N.fOut f {v})

/-- `val f = f⁺(X) − f⁻(X)`. ⚠ MUST be ℤ-valued (Headline 4).

**Book definition** (B&M §11.1, verbatim).  *Since the conservation condition
requires that the resultant flow out of any intermediate vertex is zero, it is
intuitively clear and not difficult to show (exercise 11.1.3) that, relative to any
flow `f`, the resultant flow out of `X` is equal to the resultant flow into `Y`.
This common quantity is called the value of `f`, and is denoted by `val f`; thus*

    val f = f⁺(X) - f⁻(X)

*A flow `f` in `N` is a maximum flow if there is no flow `f'` in `N` such that
`val f' > val f`.*

**Reading.**  The net rate at which the commodity travels from producers to
consumers.  Conservation at the intermediate vertices is what makes the two ways of
measuring it agree.

**Formalisation.**  ⚠ **`ℤ`-valued, and this is load-bearing.**  In `ℕ` the
truncated subtraction would make exercise 11.1.2 — the identity the whole chapter
rests on — false, since individual terms `f⁺(v) - f⁻(v)` are genuinely negative at
vertices absorbing more than they emit.  Every `f⁺ - f⁻` in this file is therefore
cast to `ℤ` before subtracting. -/
def Network.val (N : Network V) (f : V → V → ℕ) : ℤ :=
  (N.fOut f N.X : ℤ) - (N.fIn f N.X : ℤ)

/-- A **cut** `(S, S̄)` with `x ∈ S`, `y ∉ S`. ⚠ MISSING.

**Book definition** (B&M §11.2, verbatim).  *Let `N` be a network with a single
source `x` and a single sink `y`.  A cut in `N` is a set of arcs of the form
`(S, S̄)`, where `x ∈ S` and `y ∈ S̄`.*

**Reading.**  A way of severing the network so the source is on one side and the
sink on the other.  Every unit of flow must cross every cut, which is why cuts
bound flows from above (theorem 11.1) — and, more surprisingly, why the best cut
exactly matches the best flow (theorem 11.3).

**Formalisation.**  ⚠ Missing from Mathlib.  Identified with the *vertex set* `S`
rather than the arc set `(S, S̄)`, since `S` determines the arcs and is far easier
to quantify over.  `capOf` then computes the arc set's capacity.  Note `y ∉ S` is
the book's `y ∈ S̄`. -/
def Network.IsCut (N : Network V) (S : Finset V) : Prop := N.x ∈ S ∧ N.y ∉ S

/-- `cap (S, S̄) = ∑_{u∈S} ∑_{v∉S} c u v`. ⚠ MISSING.

**Book definition** (B&M §11.2, verbatim).  *The capacity of a cut `K` is the sum of
the capacities of its arcs.  We denote the capacity of `K` by `cap K`; thus
`cap K = ∑_{a ∈ K} c(a)`.*

**Reading.**  The total throughput of the severed arcs — how much traffic could at
most cross that divide.  Since all the flow must pass through, it bounds `val f`
above.

**Formalisation.**  ⚠ Missing from Mathlib.  Structurally identical to `fOut` with
`cap` in place of `f`, which is exactly why theorem 11.1's proof is a two-line
comparison. -/
def Network.capOf (N : Network V) (S : Finset V) : ℕ := ∑ u ∈ S, ∑ v ∈ Sᶜ, N.cap u v

/-- A **maximum flow**. ⚠ MISSING.

**Book definition** (B&M §11.1, verbatim).  *A flow `f` in `N` is a maximum flow if
there is no flow `f'` in `N` such that `val f' > val f`.*

**Reading.**  Ship as much as the network allows.  Theorem 11.2 characterises these
as exactly the flows admitting no incrementing path — the flow-theoretic analogue
of Berge's theorem 5.1 for matchings.

**Formalisation.**  "No flow of larger value" is stated positively as
`∀ f', IsFlow f' → val f' ≤ val f`, which is the form every consumer wants. -/
def Network.IsMaxFlow (N : Network V) (f : V → V → ℕ) : Prop :=
  N.IsFlow f ∧ ∀ f', N.IsFlow f' → N.val f' ≤ N.val f

/-- A **minimum cut**. ⚠ MISSING.

**Book definition** (B&M §11.2, verbatim).  *A cut `K` in `N` is a minimum cut if
there is no cut `K'` in `N` such that `cap K' < cap K`.*

**Reading.**  The cheapest way to sever the network — the bottleneck.  Theorem 11.3
says its capacity is exactly the maximum throughput.  B&M record the easy half
first: *If `f*` is a maximum flow and `K̃` is a minimum cut, we have, as a special
case of theorem 11.1, that `val f* ≤ cap K̃`* (11.8).

**Formalisation.**  As with `IsMaxFlow`, stated positively. -/
def Network.IsMinCut (N : Network V) (S : Finset V) : Prop :=
  N.IsCut S ∧ ∀ S', N.IsCut S' → N.capOf S ≤ N.capOf S'

/-- An `f`-**incrementing path** from the source. ⚠ MISSING from Mathlib. Honest, complete, inductive
family (static, not procedural). `fwd` = B&M's forward arc (must be `f`-unsaturated); `back` = reverse
arc (must be `f`-positive). Note this is a directed *walk* (repeated vertices allowed), which is what
Thm 11.2's proof actually uses.

**Book definition (§11.3).**  *The path `P` is `f`-unsaturated if `ι(P) > 0` (or,
equivalently, if each forward arc of `P` is `f`-unsaturated and each reverse arc of
`P` is `f`-positive).  Put simply, an `f`-unsaturated path is one that is not being
used to its full capacity.  An `f`-incrementing path is an `f`-unsaturated path
from the source `x` to the sink `y`.*

**Reading.**  A route from source to sink along which the flow can still be pushed
up.  Crucially it may travel *against* an arc — a **reverse arc** — provided that
arc currently carries positive flow, which can then be cancelled.  This is what
lets the algorithm undo earlier bad choices, exactly as an augmenting path in
matching theory rearranges an existing matching; B&M make the analogy explicit:
*the rôle played by incrementing paths in flow theory is analogous to that of
augmenting paths in matching theory* (compare theorem 5.1).  The book's example is
figure 11.5(a), where `P = xv₁v₂v₃y` is `f`-incrementing with `ι(P) = 2`.

**Formalisation.**  ⚠ Missing from Mathlib; an honest, complete inductive family —
*static*, not procedural.  `nil` starts at `N.x`; `fwd` extends along an
`f`-unsaturated arc (`f u v < cap u v`); `back` extends *against* an `f`-positive
arc (`0 < f v u`).  The index is the current endpoint, so `N.IncPath f N.y` is
exactly an `f`-incrementing path.

⚠ This is a directed **walk** — repeated vertices are allowed — not a path.  That
is deliberate and is what theorem 11.2's proof actually uses: the set `S` of
vertices reachable by `f`-unsaturated *walks* is what the cut is built from, and
restricting to paths would complicate the reachability closure for no gain. -/
inductive Network.IncPath.{u} {V : Type u} (N : Network V) (f : V → V → ℕ) : V → Type u
  | nil : Network.IncPath N f N.x
  | fwd {u v : V} : Network.IncPath N f u → f u v < N.cap u v → Network.IncPath N f v
  | back {u v : V} : Network.IncPath N f u → 0 < f v u → Network.IncPath N f v

/-- The residual capacity `ι(P) > 0` of an incrementing path — a recursion over `IncPath`.
⚠ MISSING; body deferred (needs the running-minimum bookkeeping).

**Book definition (§11.3).**  *With each path `P` in `N` we associate a
non-negative integer `ι(P) = min_{a ∈ A(P)} ι(a)`, where `ι(a) = c(a) - f(a)` if
`a` is a forward arc of `P`, and `ι(a) = f(a)` if `a` is a reverse arc.  As may
easily be seen, `ι(P)` is the largest amount by which the flow along `P` can be
increased (relative to `f`) without violating condition (11.1).*

**Reading.**  The bottleneck along the path.  A forward arc has room `c(a) - f(a)`
left; a reverse arc can give back at most the `f(a)` it currently carries.  The
smallest of these slacks is how much extra can be pushed through in one go.

**⚠ Defective: this definition has a `sorry` body.**  `ι(P)` is therefore an opaque
natural number, not the bottleneck of anything.  Consequences: exercise 11.3.1
(`revisedFlow_isFlow_and_val`) asserts `val f̂ = val f + ι(P)` about two opaque
constants and so says nothing, and the forward direction of theorem 11.2 — which
needs `ι(P) > 0` to get a strictly better flow — has no content to appeal to.
This also violates the project convention (`.claude/CLAUDE.md`): *never `sorry` in
a `def`*.

*The repair* is a structural recursion over the `IncPath` family, carrying the
running minimum:

    iota nil          = ⊤ (or: recurse with an accumulator seeded at the first arc)
    iota (fwd P h)    = min (iota P) (cap u v - f u v)
    iota (back P h)   = min (iota P) (f v u)

The only wrinkle is `nil`, which has no arcs and so no minimum; either return a
sentinel and prove `0 < iota P` for non-`nil` paths, or index the recursion by a
running minimum passed in.  The second is cleaner and avoids `ℕ∞`. -/
noncomputable def Network.IncPath.iota {N : Network V} {f : V → V → ℕ} {v : V}
    (_P : N.IncPath f v) : ℕ := sorry

/-- The revised flow `f̂` (11.9) obtained by pushing `ι(P)` along `P`. ⚠ MISSING; body deferred.

**Book definition (11.9), §11.3.**  *By sending an additional flow of `ι(P)` along
`P`, one obtains a new flow `f̂` defined by `f̂(a) = f(a) + ι(P)` if `a` is a
forward arc of `P`, `f̂(a) = f(a) - ι(P)` if `a` is a reverse arc of `P`, and
`f̂(a) = f(a)` otherwise.*

**Reading.**  Push `ι(P)` more along every forward arc of the path and take `ι(P)`
back off every reverse arc.  Conservation survives because at each interior vertex
the increase in and the increase out match; and the value rises by exactly `ι(P)`
(exercise 11.3.1).  This is the engine of the labelling method: repeatedly find an
incrementing path and revise, until none exists — at which point theorem 11.2
certifies maximality.

**⚠ Defective: this definition has a `sorry` body.**  `f̂` is an opaque function, so
exercise 11.3.1 — the only statement about it — is vacuous, and theorem 11.2's
forward direction has nothing to revise with.  Same convention violation as
`iota`.

*The repair* is a structural recursion over `IncPath` mirroring `iota`'s, adjusting
one arc per constructor:

    revisedFlow nil       = f
    revisedFlow (fwd P _) = Function.update₂ (revisedFlow P) u v (f u v + iota P)
    revisedFlow (back P _)= Function.update₂ (revisedFlow P) v u (f v u - iota P)

⚠ Note `iota P` must be the bottleneck of the **whole** path, not of the prefix, or
the capacity constraint fails on early arcs — so `iota` should be computed once and
threaded, rather than recomputed at each step.  That coupling is the reason both
definitions were deferred together, and it is why repairing `iota` first is the
right order. -/
noncomputable def Network.revisedFlow (N : Network V) {f : V → V → ℕ} {v : V}
    (_P : N.IncPath f v) : V → V → ℕ := sorry

/-!
### Local copies of the repo's connectivity API

NOTE: `SimpleGraph.InternallyDisjoint`, `vertexConnectivity` and `edgeConnectivity` live in
`TCSlib.GraphTheory.Connectivity`, which we deliberately do NOT import (keeping this file
self-contained).  The minimal local versions below are used only to *state* Cor 11.5 / Cor 11.7 /
Ex 11.4.4.  ⚠ Both connectivity numbers use `sInf` conventions (`sInf ∅ = 0`; `card V − 1` fallback
for complete graphs) that will bite at the boundaries — see the outline.
-/

open scoped Classical in
/-- Local minimal `edgeConnectivity κ'(G)` (repo has the real one).

**Book definition** (B&M §3.1, verbatim).  *We … define the edge connectivity
`κ'(G)` of `G` to be the minimum `k` for which `G` has a `k`-edge cut. …  `G` is
said to be `k`-edge-connected if `κ'(G) ≥ k`.*

**Reading.**  Corollary 11.5 relates it to edge-disjoint paths: `G` is
`k`-edge-connected exactly when any two distinct vertices are joined by `k`
edge-disjoint paths — the global connectivity number turned into a local path
count.

**Formalisation.**  A minimal local copy; the real one lives in
`TCSlib.GraphTheory.Connectivity`, deliberately not imported so this file stands
alone.  ⚠ `sInf ∅ = 0`, so a graph with no edge cut (a one-vertex graph) gets
`κ' = 0` — a boundary case that will bite corollary 11.5 exactly as it bit
chapter 10's `associatedDigraph_isKArcConnected_iff`. -/
noncomputable def edgeConnectivity (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ F : Finset (Sym2 V),
    ((F : Set (Sym2 V)) ⊆ G.edgeSet ∧ ¬ (G.deleteEdges (F : Set (Sym2 V))).Connected) ∧ F.card = n}

open scoped Classical in
/-- Local minimal `vertexConnectivity κ(G)` (repo has the real one).

**Book definition** (B&M §3.1, verbatim).  *If `G` has at least one pair of distinct
nonadjacent vertices, the connectivity `κ(G)` of `G` is the minimum `k` for which
`G` has a `k`-vertex cut; otherwise, we define `κ(G)` to be `ν - 1`. …  `G` is said
to be `k`-connected if `κ(G) ≥ k`.*

**Reading.**  Corollary 11.7 relates it to internally-disjoint paths: `G` with
`ν ≥ k + 1` is `k`-connected exactly when any two distinct vertices are joined by
`k` internally-disjoint paths.  This is the form of Menger's theorem §3.2 announced
without proof.

**Formalisation.**  A minimal local copy, as for `edgeConnectivity`.  The `ν - 1`
branch is the book's convention for graphs with no vertex cut (complete graphs).
⚠ Both `sInf` conventions bite at the boundaries — see the outline. -/
noncomputable def vertexConnectivity (G : SimpleGraph V) : ℕ :=
  if ∃ S : Finset V, (↑S : Set V) ⊂ Set.univ ∧ ¬ (G.induce ((↑S : Set V)ᶜ)).Connected then
    sInf {n : ℕ | ∃ S : Finset V,
      ((↑S : Set V) ⊂ Set.univ ∧ ¬ (G.induce ((↑S : Set V)ᶜ)).Connected) ∧ S.card = n}
  else
    Fintype.card V - 1

/-- Local minimal `InternallyDisjoint` (repo has the real one, `TwoConnected.lean:58`).

**Book definition** (B&M §3.2).  A family of paths is internally disjoint when no
vertex of `G` is an internal vertex of more than one path of the family.

**Reading.**  The paths share only their endpoints.  This is the notion in which
Menger's vertex theorem 11.7 and corollary 11.7 are phrased, and — via the vertex
splitting of theorem 11.6 — it is what *arc*-disjointness in the split digraph
corresponds to.

**Formalisation.**  A minimal local copy (the repo's is `TwoConnected.lean:58`),
stated for a **pair** of walks.  ⚠ Menger's theorem needs internal disjointness of a
whole *family*; extending this pairwise predicate to families is part of what
`maxInternallyDisjointPaths` must do, and is one reason that count was stubbed. -/
def InternallyDisjoint {G : SimpleGraph V} {u v : V} (p q : G.Walk u v) : Prop :=
  ∀ z : V, z ∈ p.support → z ∈ q.support → z = u ∨ z = v

/-!
### Extremal path counts

**⚠ All twelve of the following have `sorry` bodies, and they are the two sides of
every Menger statement.**  Consequently lemma 11.4(a)(b), theorems 11.4, 11.5,
11.6, 11.7, corollaries 11.5 and 11.7, and exercises 11.4.1 and 11.4.3 — the whole
of §11.4, and the chapter's headline application — are **vacuous**: they typecheck
but relate opaque constants and assert nothing.  Filling their proofs would
establish nothing until the definitions are repaired.

The original justification was that *none of these have an honest carrier without a
directed-path API*.  That is **too broad**.  It holds for the six directed counts,
but the six undirected ones are definable today from what this file already
imports — `SimpleGraph.Walk`, `Walk.IsPath`, `Walk.edges`, `deleteEdges`, `induce`
and the local `InternallyDisjoint`.  Each docstring below gives the specific
repair.  Schematically the two shapes are:

    max… = sSup {k | ∃ ps : Fin k → Walk x y, (∀ i, (ps i).IsPath) ∧ pairwise-disjoint ps}
    min… = sInf {k | ∃ Z, Z.card = k ∧ ¬ Reachable x y after deleting Z}

Both are `sSup`/`sInf` over sets of naturals, so they need no new carrier.  ⚠ The
`max` form needs the set bounded above for `sSup` to be meaningful — it is, by
`Fintype.card V`, but that bound must be supplied.

For the directed six, `TCSlib/GraphTheory/DirectedGraphs.lean` supplies
`Digraph.IsDirectedPath` over `Quiver.Path`; importing it would give an honest
carrier, with the caveat that arc-disjointness there routes through `arcsOf`, which
is itself `sorry`-bodied in that file.
-/

/-- Max number of arc-disjoint directed `(x,y)`-paths in a unit-ish `Network`.

**Book quantity** (B&M lemma 11.4(a), verbatim).  *…the maximum number `m` of
arc-disjoint directed `(x, y)`-paths in `N`.*

**Reading.**  For a unit-capacity network this equals the value of a maximum flow:
each path carries one unit, and arc-disjointness is exactly the capacity
constraint.

**⚠ `sorry` body.**  *Repair:* `sSup` over `k` such that there are `k` directed
`(x,y)`-paths in the underlying digraph (arcs = pairs with `0 < cap u v`) that are
pairwise arc-disjoint.  Needs a directed-path notion; see the section note. -/
noncomputable def Network.maxArcDisjointPaths (_N : Network V) : ℕ := sorry
/-- Min number of arcs whose deletion destroys all directed `(x,y)`-paths in a `Network`.

**Book quantity** (B&M lemma 11.4(b), verbatim).  *…the minimum number `n` of arcs
whose deletion destroys all directed `(x, y)`-paths in `N`.*

**Reading.**  For a unit-capacity network this equals the capacity of a minimum
cut: a cut is such a destroying set, and conversely the vertices reachable after
deleting a destroying set define a cut inside it.

**⚠ `sorry` body.**  *Repair:* `sInf {k | ∃ Z : Finset (V × V), Z.card = k ∧ ¬ Relation.ReflTransGen (fun u v => 0 < N.cap u v ∧ (u,v) ∉ Z) N.x N.y}`.
This one needs **no** directed-path API at all — reachability suffices, and
`Relation.ReflTransGen` is already imported and already used by
`maxFlow_and_minCut_zero_of_no_path`. -/
noncomputable def Network.minArcsDestroyingPaths (_N : Network V) : ℕ := sorry

/-- Max number of arc-disjoint directed `(x,y)`-paths in a digraph.

**Reading.**  The left-hand side of Menger's arc theorem 11.4: how many routes from
`x` to `y` can run simultaneously without any two sharing an arc.

**⚠ `sorry` body.**  *Repair:* `sSup` over `k` admitting `k` pairwise arc-disjoint
directed `(x,y)`-paths.  Needs a directed-path notion (`Digraph.IsDirectedPath` in
the ch-10 file) **and** an arc-list, which is `arcsOf` there — itself
`sorry`-bodied.  Of the twelve, this is the one with the deepest dependency. -/
noncomputable def maxArcDisjointDirectedPaths (_D : Digraph V) (_x _y : V) : ℕ := sorry
/-- Min number of arcs destroying all directed `(x,y)`-paths in a digraph.

**Reading.**  The right-hand side of Menger's arc theorem 11.4: how few arcs must be
cut to sever `x` from `y` entirely.

**⚠ `sorry` body.**  *Repair:* `sInf {k | ∃ Z : Finset (V × V), Z.card = k ∧ ¬ Relation.ReflTransGen (fun u v => D.Adj u v ∧ (u,v) ∉ Z) x y}`.
**No directed-path API needed** — reachability suffices. -/
noncomputable def minArcsDestroyingDirectedPaths (_D : Digraph V) (_x _y : V) : ℕ := sorry
/-- Max number of internally-disjoint directed `(x,y)`-paths in a digraph.

**Reading.**  The left-hand side of Menger's vertex theorem 11.6 — routes sharing no
intermediate vertex, so destroying any one interior station leaves the others
intact.

**⚠ `sorry` body.**  *Repair:* as for the arc version but with internal-vertex
disjointness, which needs only the paths' vertex lists (`Quiver.Path.vertices`), not
`arcsOf` — so it is easier than `maxArcDisjointDirectedPaths`. -/
noncomputable def maxInternallyDisjointDirectedPaths (_D : Digraph V) (_x _y : V) : ℕ := sorry
/-- Min number of vertices destroying all directed `(x,y)`-paths in a digraph.

**Reading.**  The right-hand side of Menger's vertex theorem 11.6 — the smallest set
of intermediate vertices whose removal severs `x` from `y`.

**⚠ `sorry` body.**  *Repair:* `sInf` over `S : Finset V` with `x ∉ S`, `y ∉ S` and
`¬ Relation.ReflTransGen (fun u v => D.Adj u v ∧ u ∉ S ∧ v ∉ S) x y`.  **No
directed-path API needed.** -/
noncomputable def minVerticesDestroyingDirectedPaths (_D : Digraph V) (_x _y : V) : ℕ := sorry

/-- Max number of edge-disjoint `(x,y)`-paths in a graph.

**Reading.**  The left-hand side of Menger's edge theorem 11.5, the undirected
counterpart of theorem 11.4.

**⚠ `sorry` body — definable today.**  *Repair:*
`sSup {k | ∃ ps : Fin k → G.Walk x y, (∀ i, (ps i).IsPath) ∧ ∀ i j, i ≠ j → List.Disjoint (ps i).edges (ps j).edges}`.
Every ingredient (`Walk`, `IsPath`, `Walk.edges`, `List.Disjoint`) is already
imported. -/
noncomputable def maxEdgeDisjointPaths (_G : SimpleGraph V) (_x _y : V) : ℕ := sorry
/-- Min number of edges destroying all `(x,y)`-paths in a graph.

**Reading.**  The right-hand side of Menger's edge theorem 11.5.

**⚠ `sorry` body — definable today.**  *Repair:*
`sInf {k | ∃ F : Finset (Sym2 V), F.card = k ∧ ¬ (G.deleteEdges ↑F).Reachable x y}`.
`deleteEdges` and `Reachable` are already imported. -/
noncomputable def minEdgesDestroyingPaths (_G : SimpleGraph V) (_x _y : V) : ℕ := sorry
/-- Max number of internally-disjoint `(x,y)`-paths in a graph.

**Reading.**  The left-hand side of Menger's vertex theorem 11.7 — the form quoted
back in §3.2, where it generalises Whitney's theorem 3.2 from `k = 2` to all `k`.

**⚠ `sorry` body — definable today.**  *Repair:* as `maxEdgeDisjointPaths` but with
`∀ i j, i ≠ j → InternallyDisjoint (ps i) (ps j)`, using the local pairwise
`InternallyDisjoint` above. -/
noncomputable def maxInternallyDisjointPaths (_G : SimpleGraph V) (_x _y : V) : ℕ := sorry
/-- Min number of vertices destroying all `(x,y)`-paths in a graph.

**Reading.**  The right-hand side of Menger's vertex theorem 11.7 — the size of a
minimum `x`–`y` vertex separator.

**⚠ `sorry` body — definable today.**  *Repair:* `sInf` over `S : Finset V` with
`x ∉ S`, `y ∉ S` and `x`, `y` unreachable in `G.induce (↑S)ᶜ`.  The only friction is
the subtype coercion on `induce`'s carrier. -/
noncomputable def minVerticesDestroyingPaths (_G : SimpleGraph V) (_x _y : V) : ℕ := sorry

/-- Max number of vertex-disjoint `S`–`T` paths (Ex 11.4.3).

**Book quantity** (B&M exercise 11.4.3, verbatim).  *…the maximum number of
vertex-disjoint paths with one end in `S` and one end in `T`.*

**Reading.**  The "fan" or set-to-set form of Menger's theorem, where the endpoints
are not fixed but merely constrained to lie in prescribed sets.  This is the form
exercise 11.4.4 (Dirac) actually consumes.

**⚠ `sorry` body — definable today.**  *Repair:* `sSup` over `k` admitting `k`
paths, each with one end in `S` and one in `T`, pairwise **vertex**-disjoint (not
merely internally disjoint — the endpoints must differ too, which is why this is not
a special case of `maxInternallyDisjointPaths`).  A `Σ`-typed family
`Fin k → Σ u ∈ S, Σ v ∈ T, G.Walk u v` handles the varying endpoints. -/
noncomputable def maxSTVertexDisjointPaths (_G : SimpleGraph V) (_S _T : Finset V) : ℕ := sorry
/-- Min number of vertices separating `S` from `T` (Ex 11.4.3).

**Book quantity** (B&M exercise 11.4.3, verbatim).  *…the minimum number of vertices
whose deletion separates `S` from `T` (that is, after deletion no component contains
a vertex of `S` and a vertex of `T`).*

**Reading.**  The set-to-set separator: a vertex set meeting every `S`–`T` route.

**⚠ `sorry` body — definable today.**  *Repair:* `sInf` over `W : Finset V` such that
in `G.induce (↑W)ᶜ` no vertex of `S \ W` is reachable from a vertex of `T \ W`.  Note
the book allows the separator to contain vertices of `S` and `T` themselves, which
the `\ W` handles. -/
noncomputable def minSTSeparator (_G : SimpleGraph V) (_S _T : Finset V) : ℕ := sorry

/-- The **associated digraph** `D(G)`: each edge becomes two opposite arcs (cited as ex 10.3.6).

**Book definition** (B&M exercise 10.3.6, verbatim).  *The associated digraph `D(G)`
of a graph `G` is the digraph obtained when each edge `e` of `G` is replaced by two
oppositely oriented arcs with the same ends as `e`.*

**Reading.**  Make every street two-way.  B&M call it *a simple trick*: it is how
theorems 11.5 and 11.7 are deduced from their directed counterparts 11.4 and 11.6,
since paths in `G` correspond exactly to directed paths in `D(G)`.

**Formalisation.**  One line — `G.Adj` is already symmetric, so it *is* the arc
relation.  A local copy of chapter 10's `SimpleGraph.associatedDigraph`; the
path correspondence that makes the trick work is that file's
`associatedDigraph_pathEquiv`, which is itself `sorry`-bodied there. -/
def associatedDigraph (G : SimpleGraph V) : Digraph V := ⟨fun u v => G.Adj u v⟩

/-- The **vertex-splitting digraph** `D'` of Theorem 11.6, on `V ⊕ V`: `inl v = v'`, `inr v = v''`,
with internal arcs `v' → v''` and each original arc `u → v` redrawn as `u'' → v'`.  ⚠ MISSING; honest
(simplified: does not special-case `x`,`y`).

**Book construction** (B&M §11.4, proof of theorem 11.6, verbatim).  *Construct a new
digraph `D'` from `D` as follows: (i) split each vertex `v ∈ V \ {x, y}` into two
new vertices `v'` and `v''`, and join them by an arc `(v', v'')`; (ii) replace each
arc of `D` with head `v ∈ V \ {x, y}` by a new arc with head `v'`, and each arc of
`D` with tail `v ∈ V \ {x, y}` by a new arc with tail `v''`.*

**Reading.**  Each vertex becomes a tiny one-way corridor `v' → v''`, so *passing
through* `v` now costs an arc.  This converts vertex-destruction into
arc-destruction, letting the vertex form of Menger's theorem be read off from the
arc form: *two directed `(x,y)`-paths in `D'` are arc-disjoint if and only if the
corresponding paths in `D` are internally-disjoint.*

**Formalisation.**  ⚠ Missing from Mathlib.  Carrier `V ⊕ V`, with `inl v = v'` and
`inr v = v''`; internal arcs are `inl u → inr v` when `u = v`, and original arcs
become `inr u → inl v`.

⚠ **Simplified: it does not special-case `x` and `y`.**  The book splits only
`V \ {x, y}`, leaving the endpoints intact; this splits *every* vertex.  The
consequence is that `x` and `y` also acquire internal arcs, so a destroying set in
`D'` could cut `x`'s or `y`'s own corridor — which corresponds to deleting `x` or
`y` themselves, something the book's vertex-destruction forbids.  Statements about
`splitDigraph` therefore address `Sum.inr x` and `Sum.inl y` (the far ends of those
corridors), which sidesteps the issue for exercise 11.4.1; but the simplification
should be checked before it is relied on elsewhere. -/
def splitDigraph (D : Digraph V) : Digraph (V ⊕ V) where
  Adj a b := match a, b with
    | Sum.inl u, Sum.inr v => u = v
    | Sum.inr u, Sum.inl v => D.Adj u v
    | _, _ => False

/-! ### Supply/demand, realisability, orientability -/

/-- **Feasibility** for supplies `σ` and demands `dem` (B&M's `∂`). ⚠ MISSING. Honest def.

**Book definition** (B&M §11.5, verbatim).  *Suppose that to each source `xᵢ` of `N`
is assigned a non-negative integer `σ(xᵢ)`, called the supply at `xᵢ`, and to each
sink `yⱼ` of `N` is assigned a non-negative integer `∂(yⱼ)`, called the demand at
`yⱼ`.  A flow `f` in `N` is said to be feasible if*

    f⁺(xᵢ) - f⁻(xᵢ) ≤ σ(xᵢ)   for all xᵢ ∈ X
    f⁻(yⱼ) - f⁺(yⱼ) ≥ ∂(yⱼ)   for all yⱼ ∈ Y

*In other words, a flow `f` is feasible if the resultant flow out of each source
`xᵢ` relative to `f` does not exceed the supply at `xᵢ`, and the resultant flow into
each sink `yⱼ` relative to `f` is at least as large as the demand at `yⱼ`.*

**Reading.**  Nobody ships more than they can produce, and everybody receives at
least what they ordered.  Gale's theorem 11.8 characterises existence: for every
`S`, the capacity out of `S` must cover the *net* demand of `S̄`.

**Formalisation.**  ⚠ Missing from Mathlib.  `dem` is B&M's `∂`.  Both conditions
are cast to `ℤ` before subtracting, for the reason recorded under `val`.  Supplies
and demands are `V → ℕ` total functions, with the conditions quantified only over
`X` and `Y`, so their values elsewhere are irrelevant. -/
def Network.IsFeasible (N : Network V) (σ dem : V → ℕ) (f : V → V → ℕ) : Prop :=
  N.IsFlow f ∧
  (∀ xi ∈ N.X, (N.fOut f {xi} : ℤ) - (N.fIn f {xi} : ℤ) ≤ (σ xi : ℤ)) ∧
  (∀ yj ∈ N.Y, (dem yj : ℤ) ≤ (N.fIn f {yj} : ℤ) - (N.fOut f {yj} : ℤ))

/-- `(p,q)` is **realisable by a simple bipartite graph**: there is a `(0,1)`-matrix `B` with row
sums `p` and column sums `q`. ⚠ MISSING (Gale–Ryser: 0 hits). Honest def.

**Book definition** (B&M §11.5, verbatim).  *We say that the pair `(p, q)` is
realisable by a simple bipartite graph if there exists a simple bipartite graph `G`
with bipartition `({x₁, x₂, …, x_m}, {y₁, y₂, …, y_n})`, such that
`d(xᵢ) = pᵢ` for `1 ≤ i ≤ m` and `d(yⱼ) = qⱼ` for `1 ≤ j ≤ n`.*

**Reading.**  Can two prescribed lists of degrees occur as the two sides of a
bipartite graph?  The book's `p = (3,2,2,2,1)`, `q = (3,3,2,1,1)` is realisable
(figure 11.12), whereas `p = q = (5,4,4,2,1)` is not (exercise 11.5.2) even though
the sums agree.

**Formalisation.**  ⚠ Missing from Mathlib (0 hits for Gale–Ryser).  Carried as a
`(0,1)`-**matrix** `B : Fin m → Fin n → Bool` rather than a bipartite `SimpleGraph`,
following the book's own closing remark: *With each simple bipartite graph `G` …
we can associate an `m × n` matrix `B` in which `b_ij = 1` or `0`, depending on
whether `xᵢyⱼ` is an edge of `G` or not.  Conversely, every `m × n` `(0,1)`-matrix
corresponds in this way to a simple bipartite graph.*  The two are equivalent and
the matrix avoids constructing a graph on `Fin m ⊕ Fin n` with a bipartition proof.
Due to Ryser (1957). -/
def RealisableBipartite {m n : ℕ} (p : Fin m → ℕ) (q : Fin n → ℕ) : Prop :=
  ∃ B : Fin m → Fin n → Bool,
    (∀ i, (Finset.univ.filter (fun j => B i j = true)).card = p i) ∧
    (∀ j, (Finset.univ.filter (fun i => B i j = true)).card = q j)

open scoped Classical in
/-- `G` is **`(m,n)`-orientable**: it admits an orientation in which every indegree is `m` or `n`.
⚠ MISSING (0 hits for `orientable`).

**Book definition** (B&M exercise 11.5.5).  *An `(m+n)`-regular graph `G` is
`(m,n)`-orientable if it can be oriented so that each indegree is either `m` or
`n`.*

**Reading.**  Make every edge one-way so each vertex ends up receiving exactly `m`
arrows, or exactly `n`.  Since `G` is `(m+n)`-regular, indegree `m` forces outdegree
`n` and conversely, so an orientation splits the vertices into two classes.
Exercise 11.5.5(a) characterises orientability by a cut condition, and (b) shows the
classes can always be rebalanced one step towards each other.

**Formalisation.**  ⚠ Missing from Mathlib (0 hits for "orientable").  The
orientation is spelled out inline as a `Digraph D` with three clauses — `D ⊆ G`, `D`
never two-way, `D` covers every edge — rather than reusing chapter 10's
`IsOrientationOf`, which this file does not import.  The fourth clause is the
indegree condition.  Note the `(m+n)`-regularity is *not* part of this definition;
it appears as a hypothesis on the theorems that use it. -/
def IsOrientable (G : SimpleGraph V) (m n : ℕ) : Prop :=
  ∃ D : Digraph V,
    (∀ u v, D.Adj u v → G.Adj u v) ∧
    (∀ u v, D.Adj u v → ¬ D.Adj v u) ∧
    (∀ u v, G.Adj u v → (D.Adj u v ∨ D.Adj v u)) ∧
    (∀ v, (Finset.univ.filter (fun u => D.Adj u v)).card = m ∨
          (Finset.univ.filter (fun u => D.Adj u v)).card = n)

open scoped Classical in
/-- `|[S, S̄]|`: the number of edges of `G` crossing the cut `(S, S̄)` (Ex 11.5.5).

**Book notation** (B&M §2.2, used in exercise 11.5.5).  `[S, S̄]` is the set of edges
with one end in `S` and the other outside.

**Reading.**  The size of the undirected edge cut at `S` — how many edges would have
to be severed to separate `S` from the rest.  In exercise 11.5.5(a) it is the
capacity available to carry the imbalance the prescribed indegrees force across
`S`'s boundary.

**Formalisation.**  A double sum of indicators rather than a `Finset.card`, matching
the shape of `fOut`/`capOf` so the three compare directly.  Since `G.Adj` is
symmetric and the sum runs over `S × Sᶜ`, each crossing edge is counted **once**. -/
noncomputable def edgeBoundaryCard (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, (if G.Adj u v then 1 else 0)

/-! ## §11.1 — Flows and cuts -/

-- Ex 11.1.2: ★ BUILD FIRST — the sum identity the whole chapter rests on (no `IsFlow` needed).
/-- **Exercise 11.1.2.**  *For any flow `f` in `N` and any `S ⊆ V`,
`∑_{v ∈ S} (f⁺(v) - f⁻(v)) = f⁺(S) - f⁻(S)`.  (Note that, in general,
`∑_{v ∈ S} f⁺(v) ≠ f⁺(S)` and `∑_{v ∈ S} f⁻(v) ≠ f⁻(S)`.)*

**Book proof.**  None — an exercise.

**Skeleton** (for `∑ v ∈ S, (f⁺{v} - f⁻{v}) = f⁺(S) - f⁻(S)` over `ℤ`).
1. **Expand everything to a double sum over `V × V`.**  Each of the four quantities
   is `∑ u ∈ A, ∑ v ∈ B, f u v` for `A`, `B` among `S`, `Sᶜ`, `{v}`, `{v}ᶜ`.
2. **Split by where the arc's ends lie.**  Every ordered pair `(u, w)` is in exactly
   one of four classes: both in `S`, both outside, `u ∈ S` only, `w ∈ S` only.
3. **The internal arcs cancel.**  For `(u, w)` with both ends in `S`, the left-hand
   side counts `f u w` once positively (in `f⁺{u}`) and once negatively (in
   `f⁻{w}`), so it contributes `0`; on the right it appears in neither term.  This
   is the whole content.
4. **The crossing arcs match.**  `u ∈ S`, `w ∉ S` contributes `+f u w` to both
   sides; `u ∉ S`, `w ∈ S` contributes `-f u w` to both.  Arcs outside `S` entirely
   contribute `0` to both.
5. Conclude by `Finset.sum_congr` / `Finset.sum_comm` bookkeeping.

**Reading.**  Summing the *net* outflow over the vertices of `S` gives the net
outflow of `S` as a whole.  The book flags the trap: *in general,
`∑_{v ∈ S} f⁺(v) ≠ f⁺(S)` and `∑_{v ∈ S} f⁻(v) ≠ f⁻(S)`* — only the difference
behaves, and only because the internal arcs cancel.

**Formalisation.**  ★ **Build this first** — lemma 11.1 and theorem 11.1 both rest on
it, and it is where the `ℤ`-valuedness of `val` earns its keep: in `ℕ` step 3's
cancellation is false, since `f⁺{v} - f⁻{v}` truncates at each vertex individually.
Note it needs **no** `IsFlow` hypothesis: it is pure bookkeeping about an arbitrary
`f`. -/
theorem sum_resultant_eq_fOut_sub_fIn (N : Network V) (f : V → V → ℕ) (S : Finset V) :
    ∑ v ∈ S, ((N.fOut f {v} : ℤ) - (N.fIn f {v} : ℤ))
      = (N.fOut f S : ℤ) - (N.fIn f S : ℤ) := by
  sorry

-- Ex 11.1.3: relative to any flow, the resultant flow out of `X` equals the resultant flow into `Y`.
/-- **Exercise 11.1.3.**  *Relative to any flow `f` in `N`, the resultant flow out of
`X` is equal to the resultant flow into `Y`.*

**Book proof.**  None — an exercise, though B&M call it *intuitively clear and not
difficult to show*.

**Skeleton** (for `f⁺(X) - f⁻(X) = f⁻(Y) - f⁺(Y)` over `ℤ`).
1. Apply exercise 11.1.2 with `S = X ∪ I`.
2. **The intermediate vertices contribute nothing.**  `hf.2` gives
   `f⁻{v} = f⁺{v}` for every `v ∈ I`, so their terms in the left-hand sum vanish
   and `f⁺(X ∪ I) - f⁻(X ∪ I) = ∑_{v ∈ X} (f⁺{v} - f⁻{v})`, which by exercise
   11.1.2 again is `f⁺(X) - f⁻(X)`.
3. **The complement of `X ∪ I` is `Y`.**  By definition `I = univ \ (X ∪ Y)` and
   `X`, `Y` are disjoint (`N.hdisj`), so `(X ∪ I)ᶜ = Y`.
4. **Flip the sides.**  `f⁺(S) = f⁻(Sᶜ)` and `f⁻(S) = f⁺(Sᶜ)` directly from the
   definitions (the double sums are the same, with the two index sets swapped).  So
   `f⁺(X ∪ I) - f⁻(X ∪ I) = f⁻(Y) - f⁺(Y)`.
5. Chain steps 2 and 4.

**Reading.**  Whatever leaves the producers must arrive at the consumers.  This is
what makes `val f` well defined — the two natural ways to measure throughput agree,
and the book *defines* `val f` as the first only after asserting they coincide.

**Formalisation.**  Step 4's `f⁺(S) = f⁻(Sᶜ)` is worth an explicit `simp` lemma; it
recurs throughout the chapter.  Step 3 is where `N.hdisj` is spent. -/
theorem fOut_X_sub_fIn_X_eq_fIn_Y_sub_fOut_Y (N : Network V) {f : V → V → ℕ} (hf : N.IsFlow f) :
    (N.fOut f N.X : ℤ) - (N.fIn f N.X : ℤ) = (N.fIn f N.Y : ℤ) - (N.fOut f N.Y : ℤ) := by
  sorry

-- Ex 11.1.4: the `N → N′` single-source/single-sink reduction.
-- TODO(ex_11_1_4): could not elaborate a faithful statement: it needs an ℕ∞-capacity single-source/
-- single-sink network `N′` built from `N` (B&M join `x` to each source "by an arc of capacity ∞"),
-- and the flow `f′` of (11.3).  The outline gives no candidate signature and the `N′` construction is
-- a whole parallel carrier (`ENat`); deferred rather than invented.

/-! ### Book statement of the deferred item

*Exercise 11.1.4.*  Show that (a) the function `f'` given by (11.3) is a flow in
`N'` with `val f' = val f`; and (b) the restriction to the arc set of `N` of a flow
in `N'` is a flow in `N` having the same value.

Here `N'` is built from `N` by adjoining new vertices `x` and `y`, joining `x` to
each source and each sink to `y` by arcs of *infinite* capacity, and designating
`x`, `y` as the single source and sink.  The correspondence (11.3) sets
`f'(a) = f(a)` on the old arcs, `f'(x, v) = f⁺(v) - f⁻(v)`, and
`f'(v, y) = f⁻(v) - f⁺(v)`.

This is what licenses the book's convention that *throughout the next three
sections, we shall confine our attention to networks that have a single source `x`
and a single sink `y`*.  As the note records, formalising it needs an
`ℕ∞`-capacity parallel carrier, so it is deferred rather than invented. -/

-- Lem 11.1: `val f = f⁺(S) − f⁻(S)` for any cut — cheapest item in the chapter.
/-- **Lemma 11.1.**  *For any flow `f` and any cut `(S, S̄)` in `N`,
`val f = f⁺(S) - f⁻(S)`.*

**Book proof** (B&M §11.2, verbatim).  *Let `f` be a flow and `(S, S̄)` a cut in `N`.
From the definitions of flow and value of a flow, we have*

    f⁺(v) - f⁻(v) = val f   if v = x
                  = 0       if v ∈ S \ {x}

*Summing these equations over `S` and simplifying (exercise 11.1.2), we obtain*

    val f = ∑_{v ∈ S} (f⁺(v) - f⁻(v)) = f⁺(S) - f⁻(S)

**Skeleton** (for `val f = f⁺(S) - f⁻(S)`, given `hf` and `hS : IsCut S`).
1. **The per-vertex identity.**  For `v = N.x`: with a single source, `val f` is by
   definition `f⁺{x} - f⁻{x}`.  ⚠ Here the file's `val` is defined as
   `f⁺(X) - f⁻(X)` over the source *set*; this step needs `X = {N.x}`, or the
   §11.1→§11.2 reduction.  See the note below.
2. For `v ∈ S \ {x}`: such a `v` is intermediate, because `y ∉ S` (`hS.2`) and the
   sinks are `Y` — so `hf.2` gives `f⁺{v} - f⁻{v} = 0`.
3. **Sum over `S` and apply exercise 11.1.2**, whose right-hand side is exactly
   `f⁺(S) - f⁻(S)`.

**Reading.**  The value of a flow can be measured across *any* cut, not just at the
source: all the material has to cross somewhere, and nothing is lost in between.
This is the observation from which theorem 11.1 immediately follows.

**⚠ Statement defect.**  This is **false as stated** — the seam between §11.1's
multi-source setting and §11.2's single-source one.  B&M close it by fiat
(*throughout the next three sections, we shall confine our attention to networks
that have a single source `x` and a single sink `y`*), but the `Network` structure
here relates `x`, `y` to `X`, `Y` in no way at all, so `val` (defined over `X`) and
the cut (separating `x` from `y`) measure different things.  The three-vertex
counterexample is worked out in full in the `Network` docstring above.  *The repair*
is the hypothesis `N.X = {N.x}` (with `N.Y = {N.y}`), either as a structure field or
on this statement.  **The skeleton assumes it** — step 1 is not derivable without
it. -/
theorem val_eq_fOut_sub_fIn (N : Network V) {f : V → V → ℕ} (hf : N.IsFlow f)
    {S : Finset V} (hS : N.IsCut S) :
    N.val f = (N.fOut f S : ℤ) - (N.fIn f S : ℤ) := by
  sorry

-- Thm 11.1: `val f ≤ cap K`.
/-- **Theorem 11.1.**  *For any flow `f` and any cut `K = (S, S̄)` in `N`,
`val f ≤ cap K`.*

**Book proof** (B&M §11.2, verbatim).  *By (11.1)*

    f⁺(S) ≤ cap K                                                    (11.6)

*and*

    f⁻(S) ≥ 0                                                        (11.7)

*We obtain (11.5) by substituting inequalities (11.6) and (11.7) in (11.4).*

**⚠ Statement defect.**  False as stated, for the same reason as lemma 11.1 — the
same three-vertex network gives `val f = 2` and `cap{x₁} = 1`.  Needs
`N.X = {N.x}`; see the `Network` docstring.  **The skeleton assumes it.**

**Skeleton** (for `val f ≤ cap S`).
1. **(11.6):** `f⁺(S) ≤ cap S`, termwise from `hf.1 : ∀ u v, f u v ≤ cap u v` and
   `Finset.sum_le_sum` twice.
2. **(11.7):** `0 ≤ f⁻(S)`, free — `f` is ℕ-valued, so the cast to `ℤ` is
   non-negative.
3. Substitute both into lemma 11.1: `val f = f⁺(S) - f⁻(S) ≤ f⁺(S) ≤ cap S`.

**Reading.**  Every unit shipped from `x` to `y` must squeeze through the cut, so no
flow can exceed the cut's throughput.  This weak-duality bound is half of the
max-flow min-cut theorem; the surprise of theorem 11.3 is that it is always
attained.  B&M record the special case immediately: `val f* ≤ cap K̃` (11.8). -/
theorem val_le_capOf (N : Network V) {f : V → V → ℕ} (hf : N.IsFlow f)
    {S : Finset V} (hS : N.IsCut S) :
    N.val f ≤ (N.capOf S : ℤ) := by
  sorry

-- Thm 11.1 (equality condition): equality iff every `(S,S̄)`-arc is saturated and every `(S̄,S)`-arc is zero.
/-- **Theorem 11.1** (equality condition).  *Equality holds in `val f ≤ cap K` if
and only if each arc in `(S, S̄)` is `f`-saturated and each arc in `(S̄, S)` is
`f`-zero.*

**Book proof** (B&M §11.2, verbatim).  *The second statement follows, on noting that
equality holds in (11.6) if and only if each arc in `(S, S̄)` is `f`-saturated, and
equality holds in (11.7) if and only if each arc in `(S̄, S)` is `f`-zero.*

The arc terminology is §11.2's: *it is convenient to call an arc `a` `f`-zero if
`f(a) = 0`, `f`-positive if `f(a) > 0`, `f`-unsaturated if `f(a) < c(a)` and
`f`-saturated if `f(a) = c(a)`.*

**⚠ Statement defect.**  Inherits lemma 11.1's — needs `N.X = {N.x}`.  **The
skeleton assumes it.**

**Skeleton** (for `val f = cap S ↔ (all (S,Sᶜ) arcs saturated) ∧ (all (Sᶜ,S) arcs zero)`).
1. By lemma 11.1, `val f = f⁺(S) - f⁻(S)`, so the goal becomes
   `f⁺(S) - f⁻(S) = cap S`.
2. With `f⁺(S) ≤ cap S` (11.6) and `0 ≤ f⁻(S)` (11.7), that equality forces **both**
   to be tight: `f⁺(S) = cap S` and `f⁻(S) = 0`.  Conversely tightness gives the
   equality.  So the goal splits into two independent equalities.
3. **`f⁺(S) = cap S ↔ all crossing arcs saturated.**  A sum of termwise-`≤` terms
   equals the total iff every term is equal — `Finset.sum_eq_sum_iff_of_le` (or
   `sum_lt_sum` for the contrapositive), applied to the double sum.
4. **`f⁻(S) = 0 ↔ all reverse arcs zero.**  A sum of naturals vanishes iff every
   term does — `Finset.sum_eq_zero_iff`.

**Reading.**  The cut is a genuine bottleneck precisely when it runs at full
capacity forwards and carries nothing backwards.  This characterisation is exactly
what the proof of theorem 11.2 verifies for the cut it constructs, which is why the
equality condition is worth stating separately rather than folding into theorem
11.1. -/
theorem val_eq_capOf_iff (N : Network V) {f : V → V → ℕ} (hf : N.IsFlow f)
    {S : Finset V} (hS : N.IsCut S) :
    N.val f = (N.capOf S : ℤ) ↔
      (∀ u ∈ S, ∀ v ∈ Sᶜ, f u v = N.cap u v) ∧ (∀ u ∈ Sᶜ, ∀ v ∈ S, f u v = 0) := by
  sorry

-- Cor 11.1: a flow and a cut of equal value are both extremal.
/-- **Corollary 11.1.**  *Let `f` be a flow and `K` a cut such that
`val f = cap K`.  Then `f` is a maximum flow and `K` is a minimum cut.*

**Book proof** (B&M §11.2, verbatim).  *Let `f*` be a maximum flow and `K̃` a minimum
cut.  Then, by (11.8),*

    val f ≤ val f* ≤ cap K̃ ≤ cap K

*Since, by hypothesis, `val f = cap K`, it follows that `val f = val f*` and
`cap K = cap K̃`.  Thus `f` is a maximum flow and `K` is a minimum cut.*

**⚠ Statement defect.**  Inherits lemma 11.1's.  In the `Network` docstring's
counterexample, `f'(x₁,y₁) = 1`, `f'(x₂,y₁) = 0` satisfies `val f' = 1 = cap{x₁}`
yet is not a maximum flow.  Needs `N.X = {N.x}`.  **The skeleton assumes it.**

**Skeleton** (for `IsMaxFlow f ∧ IsMinCut S`, given `val f = cap S`).
1. `exists_maxFlow` and `exists_minCut` supply `f*` and `K̃`.
2. **The sandwich.**  `val f ≤ val f*` (maximality of `f*`),
   `val f* ≤ cap K̃` (theorem 11.1 applied to `f*`, `K̃`), `cap K̃ ≤ cap S`
   (minimality of `K̃`).
3. The hypothesis pins the two ends equal, so every link is an equality
   (`le_antisymm` along the chain).
4. Read off both conclusions: `val f = val f*` gives `IsMaxFlow f` (using `f*`'s
   maximality to bound any other flow), and `cap S = cap K̃` gives `IsMinCut S`.

**Reading.**  The standard "weak duality certifies optimality" argument, the exact
analogue of lemma 5.3 for matchings and coverings.  It is what makes the labelling
method self-verifying: when the algorithm stops it produces a matching flow and cut,
and their equality proves both optimal. -/
theorem isMaxFlow_and_isMinCut_of_val_eq_cap (N : Network V) {f : V → V → ℕ} (hf : N.IsFlow f)
    {S : Finset V} (hS : N.IsCut S) (h : N.val f = (N.capOf S : ℤ)) :
    N.IsMaxFlow f ∧ N.IsMinCut S := by
  sorry

-- Helper (B&M silently assume existence; used by Cor 11.1 and Thm 11.3).
/-- **Existence of a maximum flow** (assumed silently by the book).

**Book proof.**  None — B&M take it for granted whenever they write *let `f*` be a
maximum flow*, as in the proof of corollary 11.1.

**Skeleton** (for `∃ f, IsMaxFlow f`).
1. **The flows form a finite nonempty set.**  A flow is determined by its values on
   `V × V`, each bounded by `cap u v`, so flows inject into
   `Π (u v : V), Fin (cap u v + 1)` — a `Fintype`.  Nonempty: the zero flow, which
   satisfies (11.1) trivially and (11.2) as `0 = 0`.
2. **Values are bounded.**  `val` is `ℤ`-valued but takes finitely many values on a
   finite set, so a maximum is attained — `Finset.exists_max_image` over the finset
   of flows, or `Set.Finite.exists_maximal_wrt`.
3. Read off `IsMaxFlow`.

**Reading.**  Nothing deep: finitely many flows, so a best one.  Worth stating
separately because corollary 11.1 and theorem 11.3 both open by invoking it, and
because the zero flow is the only reason the set is nonempty.

**Formalisation.**  Step 1 is where the ℕ-valued `f` and finite `V` pay off; note
theorem 11.1's bound is *not* needed — finiteness alone suffices, which is simpler
than the book's implicit reasoning and avoids the `X`/`x` defect. -/
theorem exists_maxFlow (N : Network V) : ∃ f : V → V → ℕ, N.IsMaxFlow f := by
  sorry

/-- **Existence of a minimum cut** (assumed silently by the book).

**Book proof.**  None — again taken for granted, as in *let `K̃` be a minimum cut*.

**Skeleton** (for `∃ S, IsMinCut S`).
1. **Cuts are a nonempty finite family.**  `S = {N.x}` is a cut provided
   `N.x ≠ N.y`; the `Finset V` are finitely many, so filter to the cuts.
2. Take one of minimum `capOf` — `Finset.exists_min_image`.
3. Read off `IsMinCut`.

**Reading.**  Finitely many subsets, at least one of them a cut, so a cheapest one.

**Formalisation.**  ⚠ Step 1 needs `N.x ≠ N.y`, which the `Network` structure does
**not** provide — `hdisj` separates `X` from `Y` but says nothing about `x` and `y`.
This is a smaller instance of the structural gap recorded in the `Network`
docstring, and the same repair (`hx`, `hy` tying `x`, `y` to `X`, `Y`) supplies it,
since `hdisj` then forces `x ≠ y`.  Without it the statement is false for a network
with `x = y`, where no cut exists. -/
theorem exists_minCut (N : Network V) : ∃ S : Finset V, N.IsMinCut S := by
  sorry

/-! ## §11.2 — Max-flow min-cut -/

-- Ex 11.2.2: no directed `(x,y)`-path ⇒ max flow value and min cut capacity are both `0`.
/-- **Exercise 11.2.2.**  *If there exists no directed `(x, y)`-path in `N`, then the
value of a maximum flow and the capacity of a minimum cut are both zero.*

**Book proof.**  None — an exercise.

**Skeleton** (for `val f = 0 ∧ capOf S = 0`).
1. **Build the witness cut.**  Let `T` be the set of vertices reachable from `N.x`
   along arcs of positive capacity — i.e. `{v | ReflTransGen (fun u w => 0 < cap u w) N.x v}`,
   as a `Finset` by decidability.  Then `N.x ∈ T` (reflexivity) and `N.y ∉ T`
   (hypothesis `h`), so `IsCut T`.
2. **`capOf T = 0`.**  Every arc out of `T` has zero capacity: a positive-capacity
   arc `u → w` with `u ∈ T` would put `w ∈ T`.  So the double sum vanishes
   (`Finset.sum_eq_zero`).
3. **`capOf S = 0`.**  `hS : IsMinCut S` gives `capOf S ≤ capOf T = 0`.
4. **`val f = 0`.**  Theorem 11.1 gives `val f ≤ capOf S = 0`; and the zero flow has
   value `0`, so `hf`'s maximality gives `0 ≤ val f`.

**Reading.**  If the sink cannot be reached at all, nothing can be shipped and
nothing needs to be cut.

**Formalisation.**  ⚠ Step 4 uses theorem 11.1, so it inherits the `X`/`x` defect
recorded in the `Network` docstring; with the repair `N.X = {N.x}` it goes through.
The hypothesis is phrased with `ReflTransGen` over positive-capacity arcs rather
than as "no directed `(x,y)`-path", which is the same thing and needs no path
API. -/
theorem maxFlow_and_minCut_zero_of_no_path (N : Network V)
    (h : ¬ Relation.ReflTransGen (fun u v => 0 < N.cap u v) N.x N.y)
    {f : V → V → ℕ} (hf : N.IsMaxFlow f) {S : Finset V} (hS : N.IsMinCut S) :
    N.val f = 0 ∧ N.capOf S = 0 := by
  sorry

-- Ex 11.2.3: minimum cuts are closed under `∪` and `∩` (submodularity; B&M give no proof).
/-- **Exercise 11.2.3.**  *If `(S, S̄)` and `(T, T̄)` are minimum cuts in `N`, then
`(S ∪ T, ...)` and `(S ∩ T, ...)` are also minimum cuts in `N`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `IsMinCut (S ∪ T) ∧ IsMinCut (S ∩ T)`).
1. **Both are cuts.**  `N.x ∈ S ∩ T` and `N.y ∉ S ∪ T` follow from `hS.1`, `hT.1`.
2. **Submodularity — the whole content.**  For *any* `S`, `T ⊆ V`,

       cap S + cap T ≥ cap (S ∪ T) + cap (S ∩ T)

   Prove it by classifying each ordered pair `(u, v)` by which of `S`, `T` contains
   `u` and which contains `v` — sixteen cases, in each of which the left side counts
   `c u v` at least as often as the right.  The only cases where the counts differ
   are `u ∈ S \ T`, `v ∈ T \ S` and its mirror, where the left counts it and the
   right does not.  Worth isolating as a standalone lemma about `capOf`.
3. **Conclude.**  Write `m` for the minimum cut capacity.  Steps 1 and the
   minimality of `S`, `T` give `cap (S∪T) ≥ m` and `cap (S∩T) ≥ m`, while step 2
   gives `cap (S∪T) + cap (S∩T) ≤ cap S + cap T = 2m`.  Hence both equal `m`.

**Reading.**  The minimum cuts form a lattice.  A consequence is that there is a
unique *smallest* minimum cut and a unique *largest* one, which is useful
algorithmically.

**Formalisation.**  Unaffected by the `X`/`x` defect — the argument is entirely about
`capOf` and `IsCut`, never about `val`.  Step 2 is a good candidate to prove first
and independently. -/
theorem isMinCut_union_inter (N : Network V) {S T : Finset V}
    (hS : N.IsMinCut S) (hT : N.IsMinCut T) :
    N.IsMinCut (S ∪ T) ∧ N.IsMinCut (S ∩ T) := by
  sorry

-- Thm 11.2: a flow is maximum iff there is no `f`-incrementing path (compare Berge).
/-- **Theorem 11.2.**  *A flow `f` in `N` is a maximum flow if and only if `N`
contains no `f`-incrementing path.*

**Book proof** (B&M §11.3, verbatim).  *If `N` contains an `f`-incrementing path
`P`, then `f` cannot be a maximum flow since `f̂`, the revised flow based on `P`, has
a larger value.*

*Conversely, suppose that `N` contains no `f`-incrementing path.  Our aim is to show
that `f` is a maximum flow.  Let `S` denote the set of all vertices to which `x` is
connected by `f`-unsaturated paths in `N`.  Clearly `x ∈ S`.  Also, since `N` has no
`f`-incrementing path, `y ∈ S̄`.  Thus `K = (S, S̄)` is a cut in `N`.  We shall show
that each arc in `(S, S̄)` is `f`-saturated and each arc in `(S̄, S)` is `f`-zero.*

*Consider an arc `a` with tail `u ∈ S` and head `v ∈ S̄`.  Since `u ∈ S`, there
exists an `f`-unsaturated `(x, u)`-path `Q`.  If `a` were `f`-unsaturated, then `Q`
could be extended by the arc `a` to yield an `f`-unsaturated `(x, v)`-path.  But
`v ∈ S̄`, and so there is no such path.  Therefore `a` must be `f`-saturated.
Similar reasoning shows that if `a ∈ (S̄, S)`, then `a` must be `f`-zero.*

*On applying theorem 11.1, we obtain `val f = cap K`.  It now follows from corollary
11.1 that `f` is a maximum flow (and that `K` is a minimum cut).*

**Skeleton** (for `IsMaxFlow f ↔ ¬ Nonempty (N.IncPath f N.y)`).
1. **(⇒), contrapositive.**  Given `P : N.IncPath f N.y`, exercise 11.3.1 gives
   `IsFlow f̂` and `val f̂ = val f + ι(P)`; with `0 < ι(P)` this beats `f`.  ⚠ Both
   `ι` and `revisedFlow` are `sorry`-bodied, so this direction currently has nothing
   to appeal to — see their docstrings.
2. **(⇐).**  Define `S := {v | Nonempty (N.IncPath f v)}`, a `Finset` by
   classical decidability.  `N.x ∈ S` via `IncPath.nil`; `N.y ∉ S` is the
   hypothesis.  So `IsCut S`.
3. **Crossing arcs are saturated.**  For `u ∈ S`, `v ∉ S`: if `f u v < cap u v` then
   `IncPath.fwd` extends `u`'s path to `v`, contradicting `v ∉ S`.  So
   `f u v = cap u v`.
4. **Reverse arcs are zero.**  For `u ∉ S`, `v ∈ S`: if `0 < f u v` then
   `IncPath.back` extends `v`'s path to `u`, contradicting `u ∉ S`.  So `f u v = 0`.
   ⚠ Watch the direction — `back` is indexed so that a positive arc `v → u` lets the
   path move backwards to reach `u`; check the constructor's orientation against
   this step.
5. **Close.**  Steps 3 and 4 are exactly the right-hand side of `val_eq_capOf_iff`,
   giving `val f = cap S`; corollary 11.1 then yields `IsMaxFlow f`.

**Reading.**  B&M stress the analogy: *the rôle played by incrementing paths in flow
theory is analogous to that of augmenting paths in matching theory* — compare
Berge's theorem 5.1.

**Formalisation.**  Note steps 2–4 are exactly where `IncPath` being a *walk* rather
than a path is convenient: `S` is a reachability closure, and closure under `fwd`
and `back` is immediate for walks.  ⚠ Step 5 uses theorem 11.1 and corollary 11.1,
so it inherits the `X`/`x` defect. -/
theorem maxFlow_iff_no_incrementing_path (N : Network V) {f : V → V → ℕ} (hf : N.IsFlow f) :
    N.IsMaxFlow f ↔ ¬ Nonempty (N.IncPath f N.y) := by
  sorry

-- Thm 11.2 (★ extracted cut lemma — Thm 11.3 needs this, cannot get it from Thm 11.2's statement).
/-- **Extracted from the proof of theorem 11.2.**  *If `N` contains no
`f`-incrementing path, then there is a cut `K` with `val f = cap K`.*

**Book proof.**  Not stated separately — it is steps 2–5 of theorem 11.2's converse,
which B&M then reuse: *in the course of the above proof, we established the
existence of a maximum flow `f` and a minimum cut `K` such that `val f = cap K`.*

**Skeleton** (for `∃ S, IsCut S ∧ val f = cap S`).
1–4. Exactly steps 2–4 of `maxFlow_iff_no_incrementing_path`: build
   `S := {v | Nonempty (N.IncPath f v)}`, show `IsCut S`, and show every crossing arc
   is saturated and every reverse arc zero.
5. Apply `val_eq_capOf_iff` in the `←` direction to get `val f = cap S`, and return
   `⟨S, _, _⟩`.

**Reading.**  The constructive core of theorem 11.2's converse: the cut built from
the `f`-unsaturated reachability set has capacity exactly `val f`.

**Formalisation.**  ★ This has to be **extracted separately** because theorem 11.2's
*statement* asserts only maximality and discards the cut, while theorem 11.3 needs
the cut itself.  Fill this one first and derive theorem 11.2's converse from it,
rather than the other way round — otherwise the reachability construction has to be
written twice. -/
theorem exists_cut_of_no_incrementing_path (N : Network V) {f : V → V → ℕ} (hf : N.IsFlow f)
    (h : ¬ Nonempty (N.IncPath f N.y)) :
    ∃ S : Finset V, N.IsCut S ∧ N.val f = (N.capOf S : ℤ) := by
  sorry

-- Thm 11.3: ★ THE MAX-FLOW MIN-CUT THEOREM (Ford & Fulkerson, 1956).
/-- **Theorem 11.3** (the max-flow min-cut theorem; Ford and Fulkerson, 1956).  *In
any network, the value of a maximum flow is equal to the capacity of a minimum
cut.*

**Book proof.**  None given separately — B&M derive it from the *proof* of theorem
11.2 rather than from its statement: *In the course of the above proof, we
established the existence of a maximum flow `f` and a minimum cut `K` such that
`val f = cap K`.  We thus have the following theorem, due to Ford and Fulkerson
(1956).*

**⚠ Statement defect.**  Inherits lemma 11.1's.  In the `Network` docstring's
counterexample the maximum flow value is `2` while the minimum cut capacity is `1`,
so this asserts `2 = 1`.  Needs `N.X = {N.x}`.  **The skeleton assumes it.**

**Skeleton** (for `∃ f S, IsMaxFlow f ∧ IsMinCut S ∧ val f = cap S`).
1. `exists_maxFlow` gives a maximum flow `f`.
2. Theorem 11.2 (⇒) gives that `f` admits no incrementing path.
3. `exists_cut_of_no_incrementing_path` produces `S` with `IsCut S` and
   `val f = cap S`.
4. Corollary 11.1 upgrades `IsCut S` to `IsMinCut S` (and re-certifies `f`).
5. Return `⟨f, S, _, _, _⟩`.

**Reading.**  Theorem 11.1 gave the easy half — `val f ≤ cap K` for every flow and
cut; this says the bound is always achieved, so the bottleneck is not merely an
upper limit but the exact answer.  B&M call it *of central importance in graph
theory*: *many results on graphs turn out to be easy consequences of this theorem as
applied to suitably chosen networks*, as §§11.4 and 11.5 demonstrate with Menger's
theorems and the Gale–Ryser criterion.

*The labelling method* (Ford and Fulkerson, 1957), which the constructive proof
yields: start from the zero flow and repeatedly grow an `f`-unsaturated tree from
`x`, until either it reaches `y` (**breakthrough**, giving an incrementing path to
revise along) or it stops growing (certifying maximality by theorem 11.2).  B&M note
it is *not* a good algorithm — figure 11.9 gives a network needing `2m + 1`
iterations for arbitrary `m` — but Edmonds and Karp (1970) showed that scanning
"first-labelled first-scanned", i.e. always taking a *shortest* incrementing path,
makes it good.

**Formalisation.**  Steps 1–4 are all already-stated results, so this theorem is
five lines once its inputs are filled — but it sits at the top of the dependency
chain and inherits every defect below it, including the `sorry`-bodied `ι` and
`revisedFlow` via step 2. -/
theorem maxFlow_min_cut (N : Network V) :
    ∃ (f : V → V → ℕ) (S : Finset V),
      N.IsMaxFlow f ∧ N.IsMinCut S ∧ N.val f = (N.capOf S : ℤ) := by
  sorry

/-! ## §11.3 — The revised flow -/

/-! ## §11.4 — Menger's theorems -/

-- Lem 11.4(a): in a unit-capacity network, max flow value = max number of arc-disjoint paths.
/-- **Lemma 11.4(a).**  *Let `N` be a network with source `x` and sink `y` in which
each arc has unit capacity.  Then the value of a maximum flow in `N` is equal to
the maximum number `m` of arc-disjoint directed `(x, y)`-paths in `N`.*

**Book proof** (B&M §11.4, verbatim).  *Let `f*` be a maximum flow in `N` and let
`D*` denote the digraph obtained from `D` by deleting all `f*`-zero arcs.  Since
each arc of `N` has unit capacity, `f*(a) = 1` for all `a ∈ A(D*)`.  It follows
that*

    (i)  d⁺_{D*}(x) - d⁻_{D*}(x) = val f* = d⁻_{D*}(y) - d⁺_{D*}(y)
    (ii) d⁺_{D*}(v) = d⁻_{D*}(v)   for all v ∈ V \ {x, y}

*Therefore (exercise 10.3.3) there exist `val f*` arc-disjoint directed
`(x, y)`-paths in `D*`, and hence also in `D`.  Thus `val f* ≤ m` (11.10).*

*Now let `P₁, P₂, …, P_m` be any system of `m` arc-disjoint directed `(x, y)`-paths
in `N`, and define a function `f` on `A` by `f(a) = 1` if `a` is an arc of
`⋃ Pᵢ`, and `0` otherwise.  Clearly `f` is a flow in `N` with value `m`.  Since
`f*` is a maximum flow, we have `val f* ≥ m` (11.11).  It now follows from (11.10)
and (11.11) that `val f* = m`.*

**⚠ Currently vacuous.**  `N.maxArcDisjointPaths` has a `sorry` body, so the
right-hand side is an opaque constant.  See the section note above the extremal
path counts.

**Skeleton** (for `val f = maxArcDisjointPaths`, assuming that count is repaired).
1. **`val f ≤ m`.**  Let `D*` be the positive-flow arcs.  Unit capacity plus
   `hunit` forces `f a ∈ {0, 1}`, so `f = 1` throughout `D*`.  Read off the degree
   conditions (i), (ii) from `IsFlow`.  Then invoke **chapter 10's exercise 10.3.3**
   (`exists_arcDisjoint_directedPaths`) to extract `val f` arc-disjoint paths.
2. **`val f ≥ m`.**  Given `m` arc-disjoint paths, set `f' = 1` on their arcs, `0`
   elsewhere.  Capacity: each arc is on at most one path, so `f' ≤ 1 ≤ cap`.
   Conservation: each interior vertex of each path is entered once and left once.
   Value `m`: the `m` paths each contribute one unit out of `x`.  Then `hf`'s
   maximality gives `val f ≥ m`.
3. `le_antisymm`.

**Reading.**  With unit capacities a flow *is* a packing of arc-disjoint routes, each
carrying one unit.  This lemma is the bridge from flow theory to Menger.

**Formalisation.**  ⚠ Two imported dependencies, both currently defective: step 1
needs chapter 10's exercise 10.3.3, whose statement there mentions the
`sorry`-bodied `arcsOf`; and B&M's proof of *that* exercise adds `l` parallel arcs,
which neither `Digraph` nor this file's `cap : V → V → ℕ` carrier can express.  ⚠
Also note `hunit : ∀ u v, cap u v ≤ 1` permits `cap = 0`, i.e. absent arcs, which is
what the book means by "each arc has unit capacity"; that reading is correct here. -/
theorem unitCapacity_maxFlow_eq_arcDisjoint (N : Network V) (hunit : ∀ u v, N.cap u v ≤ 1)
    {f : V → V → ℕ} (hf : N.IsMaxFlow f) :
    N.val f = (N.maxArcDisjointPaths : ℤ) := by
  sorry

-- Lem 11.4(b): in a unit-capacity network, min cut capacity = min number of arcs destroying all paths.
/-- **Lemma 11.4(b).**  *In a unit-capacity network, the capacity of a minimum cut
is equal to the minimum number `n` of arcs whose deletion destroys all directed
`(x, y)`-paths.*

**Book proof** (B&M §11.4, verbatim).  *Let `K̃ = (S, S̄)` be a minimum cut in `N`.
Then, in `N - K̃`, no vertex of `S̄` is reachable from any vertex in `S`; in
particular, `y` is not reachable from `x`.  Thus `K̃` is a set of arcs whose deletion
destroys all directed `(x, y)`-paths, and we have `cap K̃ = |K̃| ≥ n` (11.12).*

*Now let `Z` be a set of `n` arcs whose deletion destroys all directed
`(x, y)`-paths, and denote by `S` the set of all vertices reachable from `x` in
`N - Z`.  Since `x ∈ S` and `y ∈ S̄`, `K = (S, S̄)` is a cut in `N`.  Moreover, by the
definition of `S`, `N - Z` can contain no arc of `(S, S̄)`, and so `K ⊆ Z`.  Since
`K̃` is a minimum cut, we conclude that `cap K̃ ≤ cap K = |K| ≤ |Z| = n` (11.13).
Together, (11.12) and (11.13) now yield `cap K̃ = n`.*

**⚠ Currently vacuous.**  `N.minArcsDestroyingPaths` has a `sorry` body.  Note this
one is the *easiest* of the twelve to repair — reachability suffices, no path API
needed; see its docstring.

**Skeleton** (for `capOf S = minArcsDestroyingPaths`, assuming that count is
repaired).
1. **`cap S ≥ n` (11.12).**  The arcs of the cut `(S, Sᶜ)` form a destroying set:
   after deleting them, reachability from `N.x` cannot leave `S`, and `N.y ∉ S`.
   With unit capacities `cap S` is the *number* of those arcs, so it is one of the
   sizes over which `n` is the infimum.
2. **`cap S ≤ n` (11.13).**  Given a destroying set `Z` of size `n`, let
   `T := {v | reachable from N.x in N - Z}`.  Then `IsCut T`, every arc of
   `(T, Tᶜ)` lies in `Z` (else its head would be reachable), so
   `cap T ≤ |Z| = n`; and `hS`'s minimality gives `cap S ≤ cap T`.
3. `le_antisymm`.

**Reading.**  With part (a) and the max-flow min-cut theorem, this immediately yields
Menger's arc theorem 11.4 — the whole of §11.4 rests on these two halves.

**Formalisation.**  ⚠ Step 1 uses that with unit capacities `cap S` counts arcs; this
needs `hunit` *and* that every counted arc actually exists (`cap u v = 1`, not `0`),
so the sum-to-cardinality step deserves care. -/
theorem unitCapacity_minCut_eq_minDestroying (N : Network V) (hunit : ∀ u v, N.cap u v ≤ 1)
    {S : Finset V} (hS : N.IsMinCut S) :
    N.capOf S = N.minArcsDestroyingPaths := by
  sorry

-- Thm 11.4: Menger, arc version, digraphs.
/-- **Theorem 11.4** (Menger, 1927; arc version for digraphs).  *Let `x` and `y` be
two vertices of a digraph `D`.  Then the maximum number of arc-disjoint directed
`(x, y)`-paths in `D` is equal to the minimum number of arcs whose deletion
destroys all directed `(x, y)`-paths in `D`.*

**Book proof** (B&M §11.4, verbatim).  *We obtain a network `N` with source `x` and
sink `y` by assigning unit capacity to each arc of `D`.  The theorem now follows
from lemma 11.4 and the max-flow min-cut theorem (11.3).*

**⚠ Currently vacuous.**  Both sides have `sorry` bodies.

**Skeleton** (for `maxArcDisjointDirectedPaths D x y = minArcsDestroyingDirectedPaths D x y`).
1. **Build the unit-capacity network.**  `cap u v := if D.Adj u v then 1 else 0`,
   with `X = {x}`, `Y = {y}` — note this automatically satisfies the `N.X = {N.x}`
   repair that §11.2 needs, so the defect does not bite here.
2. Lemma 11.4(a): `val (max flow) = maxArcDisjointPaths N`, which must then be
   identified with `maxArcDisjointDirectedPaths D x y` — a bookkeeping step between
   the network-level and digraph-level counts.
3. Lemma 11.4(b): `cap (min cut) = minArcsDestroyingPaths N`, likewise identified
   with `minArcsDestroyingDirectedPaths D x y`.
4. Theorem 11.3 equates the two middles; chain.

**Reading.**  The number of independent routes you can run equals the number of links
an adversary must cut to stop you.  This is the first of the four Menger theorems
the chapter derives — arc/edge and vertex versions, for digraphs and graphs — two of
which were quoted without proof back in §3.2.

**Formalisation.**  ⚠ Steps 2 and 3 are not free: the network-level counts
(`Network.maxArcDisjointPaths`) and the digraph-level ones
(`maxArcDisjointDirectedPaths`) are *separate* stubbed definitions, so once both are
repaired a lemma identifying them across the construction of step 1 will be needed.
Defining the network-level pair *in terms of* the digraph-level pair applied to the
underlying digraph would make steps 2–3 definitional and is the better design. -/
theorem menger_arc_digraph (D : Digraph V) (x y : V) :
    maxArcDisjointDirectedPaths D x y = minArcsDestroyingDirectedPaths D x y := by
  sorry

-- Thm 11.5: Menger, edge version, graphs ("a simple trick" via `D(G)`; also needs ex 10.3.6).
/-- **Theorem 11.5** (Menger; edge version for graphs).  *Let `x` and `y` be two
vertices of a graph `G`.  Then the maximum number of edge-disjoint `(x, y)`-paths
in `G` is equal to the minimum number of edges whose deletion destroys all
`(x, y)`-paths in `G`.*

**Book proof** (B&M §11.4, verbatim).  *Apply theorem 11.4 to `D(G)`, the associated
digraph of `G` (exercise 10.3.6).*

**⚠ Currently vacuous.**  Both sides have `sorry` bodies — though both are among the
six **definable today**; see their docstrings.

**Skeleton** (for `maxEdgeDisjointPaths G x y = minEdgesDestroyingPaths G x y`).
1. Apply theorem 11.4 to `associatedDigraph G`.
2. **Transfer the max side.**  Paths in `G` correspond to directed paths in `D(G)`
   (exercise 10.3.6), and *edge*-disjointness to *arc*-disjointness.  ⚠ This needs
   care: each edge of `G` becomes **two** arcs in `D(G)`, so two `G`-paths sharing
   an edge might traverse it in opposite directions and be arc-disjoint in `D(G)`.
   The correspondence is still right — a system of edge-disjoint paths maps to
   arc-disjoint ones and conversely, after orienting each path along its own
   direction — but the "conversely" is the step B&M's *simple trick* elides.
3. **Transfer the min side.**  Deleting an edge of `G` deletes both its arcs; a
   minimum arc-destroying set may be assumed closed under this pairing, since
   keeping one direction of an edge never helps destroy paths in an undirected
   graph.
4. Chain.

**Reading.**  The undirected Menger theorem quoted in §3.2 as the edge analogue of
Whitney's theorem 3.2.

**Formalisation.**  Step 2's caveat is the one place where "a simple trick
immediately yields" is doing real work; budget for it. -/
theorem menger_edge_graph (G : SimpleGraph V) (x y : V) :
    maxEdgeDisjointPaths G x y = minEdgesDestroyingPaths G x y := by
  sorry

-- Cor 11.5: `k`-edge-connected ⇔ any two distinct vertices joined by `k` edge-disjoint paths.
-- NOTE: uses the local `edgeConnectivity` (repo's lives in the un-imported Connectivity file);
-- B&M's `edgeConnectivity` is global, this relates it to local `x`–`y` separation.
/-- **Corollary 11.5.**  *A graph `G` is `k`-edge-connected if and only if any two
distinct vertices of `G` are connected by at least `k` edge-disjoint paths.*

**Book proof** (B&M §11.4, verbatim).  *This follows directly from theorem 11.5 and
the definition of `k`-edge-connectedness.*

**⚠ Currently vacuous** on the right — `maxEdgeDisjointPaths` has a `sorry` body.

**Skeleton** (for `k ≤ edgeConnectivity G ↔ ∀ u v, u ≠ v → k ≤ maxEdgeDisjointPaths G u v`).
1. **Key bridge:** `edgeConnectivity G = ⨅ (u ≠ v), minEdgesDestroyingPaths G u v`.
   A set of edges disconnects `G` iff it separates *some* pair, so the global
   minimum is the minimum over pairs of the local minima.  Prove this first; it is
   where "the definition of `k`-edge-connectedness" is unpacked.
2. Theorem 11.5 rewrites each local `minEdgesDestroyingPaths` as
   `maxEdgeDisjointPaths`.
3. `k ≤ ⨅ …` unfolds to `∀ pairs, k ≤ …`, giving the `↔`.

**Reading.**  `k`-edge-connectedness says no `k - 1` edges disconnect the graph; by
theorem 11.5 the minimum number of edges separating a *specific* pair equals the
maximum number of edge-disjoint paths between them.  Minimising over pairs converts
the global statement into the local one.  This is the edge form of Menger's theorem
quoted without proof in §3.2, generalising exercise 3.2.1 (`k = 2`) to all `k`.

**Formalisation.**  Uses the local `edgeConnectivity` copy.  ⚠ Watch the `sInf ∅ = 0`
boundary flagged there: on a one-vertex graph no edge cut exists, so
`edgeConnectivity = 0`, while the right-hand side is vacuously true for every `k`
(there is no pair `u ≠ v`).  So the `↔` fails at `k ≥ 1`, `card V ≤ 1` — a
`[Nontrivial V]` hypothesis is the fix, exactly as in chapter 10's
`associatedDigraph_isKArcConnected_iff`. -/
theorem k_edge_connected_iff_edge_disjoint_paths (G : SimpleGraph V) (k : ℕ) :
    k ≤ edgeConnectivity G ↔
      ∀ u v : V, u ≠ v → k ≤ maxEdgeDisjointPaths G u v := by
  sorry

-- Thm 11.6: Menger, vertex version, digraphs.
/-- **Theorem 11.6** (Menger; vertex version for digraphs).  *Let `x` and `y` be two
vertices of a digraph `D` such that `x` is not joined to `y`.  Then the maximum
number of internally-disjoint directed `(x, y)`-paths in `D` is equal to the
minimum number of vertices whose deletion destroys all directed `(x, y)`-paths.*

**Book proof** (B&M §11.4, verbatim).  *Construct a new digraph `D'` from `D` as
follows: (i) split each vertex `v ∈ V \ {x, y}` into two new vertices `v'` and
`v''`, and join them by an arc `(v', v'')`; (ii) replace each arc of `D` with head
`v ∈ V \ {x, y}` by a new arc with head `v'`, and each arc of `D` with tail
`v ∈ V \ {x, y}` by a new arc with tail `v''`.*

*Now to each directed `(x, y)`-path in `D'` there corresponds a directed
`(x, y)`-path in `D` obtained by contracting all arcs of type `(v', v'')`; and,
conversely, to each directed `(x, y)`-path in `D`, there corresponds a directed
`(x, y)`-path in `D'` obtained by splitting each internal vertex of the path.
Furthermore, two directed `(x, y)`-paths in `D'` are arc-disjoint if and only if the
corresponding paths in `D` are internally-disjoint.  It follows that the maximum
number of arc-disjoint directed `(x, y)`-paths in `D'` is equal to the maximum
number of internally-disjoint directed `(x, y)`-paths in `D`.  Similarly, the
minimum number of arcs in `D'` whose deletion destroys all directed `(x, y)`-paths
is equal to the minimum number of vertices in `D` whose deletion destroys all
directed `(x, y)`-paths (exercise 11.4.1).  The theorem now follows from theorem
11.4.*

**⚠ Currently vacuous.**  Both sides have `sorry` bodies.

**Skeleton** (for `maxInternallyDisjointDirectedPaths D x y = minVerticesDestroyingDirectedPaths D x y`).
1. **The path correspondence.**  Directed `(x,y)`-paths in `D'` ↔ in `D`, by
   contracting / splitting the internal arcs.  A mutual construction plus two round
   trips.
2. **Disjointness matches.**  Two `D'`-paths are arc-disjoint iff the corresponding
   `D`-paths are internally disjoint — sharing an interior vertex `v` means sharing
   the arc `(v', v'')`.  This is the crux and is why the splitting works at all.
3. Steps 1–2 give the max sides equal; exercise 11.4.1 gives the min sides equal.
4. Theorem 11.4 applied to `D'` equates the two middles; chain.

**Reading.**  ⚠ The hypothesis `¬ D.Adj x y` is load-bearing: an arc `(x, y)` cannot
be destroyed by deleting *intermediate* vertices, so without it the right-hand side
would be unattainable while the left is at least `1`.

**Formalisation.**  ⚠ Step 1 must contend with `splitDigraph` splitting `x` and `y`
as well, contrary to the book — see that definition's docstring.  Concretely, a
`D'`-path from `inr x` to `inl y` never traverses `x`'s or `y`'s corridor, so the
correspondence is unharmed; but that fact needs stating rather than assuming. -/
theorem menger_vertex_digraph (D : Digraph V) (x y : V) (h : ¬ D.Adj x y) :
    maxInternallyDisjointDirectedPaths D x y = minVerticesDestroyingDirectedPaths D x y := by
  sorry

-- Thm 11.7: ★ Menger, vertex version, graphs (apply Thm 11.6 to `D(G)`; also needs ex 10.3.6).
/-- **Theorem 11.7** (Menger; vertex version for graphs).  *Let `x` and `y` be two
nonadjacent vertices of a graph `G`.  Then the maximum number of
internally-disjoint `(x, y)`-paths in `G` is equal to the minimum number of
vertices whose deletion destroys all `(x, y)`-paths.*

**Book proof** (B&M §11.4, verbatim).  *Apply theorem 11.6 to `D(G)`, the associated
digraph of `G`.*

**⚠ Currently vacuous.**  Both sides have `sorry` bodies, though both are among the
six **definable today**.

**Skeleton** (for `maxInternallyDisjointPaths G x y = minVerticesDestroyingPaths G x y`).
1. Apply theorem 11.6 to `associatedDigraph G`; its hypothesis `¬ D.Adj x y` is
   this statement's `h : ¬ G.Adj x y`, since `D(G).Adj = G.Adj`.
2. **Transfer the max side.**  `G`-paths ↔ directed `D(G)`-paths (exercise 10.3.6),
   and internal disjointness is preserved in both directions — this transfer is
   cleaner than theorem 11.5's, because internal disjointness is about *vertices*
   and so is insensitive to the doubling of edges into arcs.
3. **Transfer the min side.**  Vertex-destroying sets are literally the same objects
   on both sides, `D(G)` having the same vertex set as `G`.
4. Chain.

**Reading.**  The most quoted form of Menger's theorem, and the one §3.2 announced
without proof.  The number of independent routes between two stations equals the
number of intermediate stations an adversary must destroy to sever them — the vertex
analogue of max-flow min-cut duality, specialising at `k = 2` to Whitney's theorem
3.2.

**Formalisation.**  Note step 2 is genuinely easier than the corresponding step of
theorem 11.5, so this is the better of the two undirected Menger theorems to attempt
first. -/
theorem menger_vertex_graph (G : SimpleGraph V) (x y : V) (h : ¬ G.Adj x y) :
    maxInternallyDisjointPaths G x y = minVerticesDestroyingPaths G x y := by
  sorry

-- Cor 11.7: `k`-connected ⇔ any two distinct vertices joined by `k` internally-disjoint paths.
-- NOTE: uses the local `vertexConnectivity`.  ⚠ B&M's "immediate" is FALSE (adjacent case is separate
-- work); the `k = 2` case is fully proved in the repo (`TwoConnected.lean:537`).
/-- **Corollary 11.7.**  *A graph `G` with `ν ≥ k + 1` is `k`-connected if and only
if any two distinct vertices of `G` are connected by at least `k`
internally-disjoint paths.*

**Book proof.**  None — B&M write only *The following corollary is immediate.*

**⚠ Currently vacuous** on the right — `maxInternallyDisjointPaths` has a `sorry`
body.

**Skeleton** (for `k ≤ vertexConnectivity G ↔ ∀ u v, u ≠ v → k ≤ maxInternallyDisjointPaths G u v`).
1. **Bridge, nonadjacent pairs.**  As in corollary 11.5:
   `vertexConnectivity G = ⨅ over nonadjacent pairs, minVerticesDestroyingPaths G u v`,
   then theorem 11.7 rewrites each term.
2. **⚠ The adjacent case is separate work.**  Theorem 11.7 requires `¬ G.Adj u v`,
   so for an adjacent pair the bridge gives nothing.  The standard repair: apply the
   theorem to `G - uv`, obtaining `k - 1` internally-disjoint paths there, and add
   the edge `uv` itself as a further path — giving `k`.  Establishing that
   `κ(G - uv) ≥ κ(G) - 1` is the part to budget for.
3. Combine the two cases.

**Reading.**  `k`-connectivity says no `k - 1` vertices disconnect the graph; theorem
11.7 converts the local separation number for a nonadjacent pair into a path count,
and minimising over pairs converts global into local.

**Formalisation.**  ⚠ B&M call this *immediate*; it is not — step 2 is genuine work,
and the `k = 2` case alone is a full proof in the repo (`TwoConnected.lean:537`).
Uses the local `vertexConnectivity`, whose `ν - 1` fallback for complete graphs
interacts with step 2 (a complete graph has *only* adjacent pairs), so check that
boundary.  `h : k + 1 ≤ card V` is the book's `ν ≥ k + 1`. -/
theorem k_connected_iff_internally_disjoint_paths (G : SimpleGraph V) (k : ℕ)
    (h : k + 1 ≤ Fintype.card V) :
    k ≤ vertexConnectivity G ↔
      ∀ u v : V, u ≠ v → k ≤ maxInternallyDisjointPaths G u v := by
  sorry

-- Ex 11.4.4*: Dirac — any `k` vertices of a `k`-connected graph (`k ≥ 2`) lie on a common cycle.
/-- **Exercise 11.4.4*** (Dirac).  *If `G` is `k`-connected with `k ≥ 2`, then any
`k` vertices of `G` are contained together in some cycle.*

**Book proof.**  None — an exercise, and one the book **stars**.

**Skeleton** (for `∃ w c, c.IsCycle ∧ ∀ v ∈ T, v ∈ c.support`).
1. **Take a cycle capturing as many of `T` as possible.**  `k ≥ 2` and
   `k`-connectivity give at least one cycle (2-connected graphs are not forests), so
   the family of cycles is nonempty; maximise `|T ∩ support|` over it.
2. `by_contra`: suppose some `v ∈ T` is off the chosen cycle `C`.
3. **Fan from `v` to `C`.**  Exercise 11.4.3 with `S = {v}` and `T = V(C)`: since
   `G` is `k`-connected, no set of fewer than `k` vertices separates `v` from `C`,
   so there are `min(k, |V(C)|)` vertex-disjoint `v`–`C` paths.
4. **Splice two of them in.**  Two of those paths meet `C` at points that divide it
   into two arcs; replacing one arc by the two paths through `v` gives a longer
   cycle containing `v`.  Choose the two landing points so that the discarded arc
   contains **no** vertex of `T` — possible because there are `k` paths and at most
   `k - 1` other `T`-vertices to avoid.  ⚠ This choice is the crux and is where
   `hT : T.card = k` is spent.
5. The new cycle captures strictly more of `T`, contradicting step 1.

**Reading.**  High connectivity forces any prescribed set of `k` vertices onto a
single cycle.  For `k = 2` this is corollary 3.2.1 — in a 2-connected graph any two
vertices lie on a common cycle.  One of the classic applications of Menger's
theorem, illustrating B&M's remark that *many results on graphs turn out to be easy
consequences* of max-flow min-cut.

**Formalisation.**  Depends on exercise 11.4.3, hence on two `sorry`-bodied
definitions; but note the *statement* here mentions none of them — it is about
`Walk`/`IsCycle` only, so it is well-formed and would be meaningful once its
dependency is repaired.  Among the §11.4 items, this is the one whose statement is
already honest. -/
theorem dirac_k_vertices_on_cycle (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k)
    (hconn : k ≤ vertexConnectivity G) (T : Finset V) (hT : T.card = k) :
    ∃ (w : V) (c : G.Walk w w), c.IsCycle ∧ ∀ v ∈ T, v ∈ c.support := by
  sorry

/-! ## §11.5 — Feasible flows and realisability -/

-- Ex 11.5.1: ★ build before Thm 11.8 — `N` has a feasible flow iff `N′` saturates each arc of `(Y,{y})`.
-- TODO(ex_11_5_1): could not elaborate a faithful statement: it depends on the `N′` construction
-- inside Thm 11.8's proof (adjoin a super-source/super-sink with supply/demand capacities), which the
-- outline flags as MISSING and gives no signature for.  Deferred rather than invented.

/-! ### Book statement of the deferred item

*Exercise 11.5.1.*  Show that the network `N` in the proof of theorem 11.8 has a
feasible flow if and only if `N'` has a flow that saturates each arc of the cut
`(Y, {y})`.

Here `N'` is built from `N` by adjoining new vertices `x` and `y`, joining `x` to
each source `xᵢ` by an arc of capacity `σ(xᵢ)` and each sink `yⱼ` to `y` by an arc
of capacity `∂(yⱼ)`.  Saturating every arc into `y` means every demand is exactly
met, which is precisely feasibility back in `N`; and such a flow has value
`∂(Y) = cap(Y, {y})`, so by corollary 11.1 it is a maximum flow.

As the note records, formalising this needs the `N'` construction, for which the
outline gives no signature; it is deferred rather than invented. -/

-- Thm 11.8: Gale's feasible-flow theorem (Gale, 1957).
/-- **Theorem 11.8** (Gale, 1957).  *There exists a feasible flow in `N` if and only
if, for all `S ⊆ V`, `c(S, S̄) ≥ ∂(Y ∩ S̄) - σ(X ∩ S̄)`.*

**Book proof** (B&M §11.5, verbatim).  *Construct a new network `N'` from `N` as
follows: (i) adjoin two new vertices `x` and `y` to `N`; (ii) join `x` to each
`xᵢ ∈ X` by an arc of capacity `σ(xᵢ)`; (iii) join each `yⱼ ∈ Y` to `y` by an arc of
capacity `∂(yⱼ)`; (iv) designate `x` as the source and `y` as the sink of `N'`.*

*It is not difficult to see that `N` has a feasible flow if and only if `N'` has a
flow that saturates each arc of the cut `(Y, {y})` (exercise 11.5.1).  Now a flow in
`N'` that saturates each arc of `(Y, {y})` clearly has value
`∂(Y) = cap(Y, {y})`, and is therefore, by corollary 11.1, a maximum flow.  It
follows that `N` has a feasible flow if and only if, for each cut
`(S ∪ {x}, S̄ ∪ {y})` of `N'`,*

    cap(S ∪ {x}, S̄ ∪ {y}) ≥ ∂(Y)                                     (11.15)

*But conditions (11.14) and (11.15) are precisely the same; for, denoting the
capacity function in `N'` by `c'`, we have*

    cap(S ∪ {x}, S̄ ∪ {y}) = c'(S, S̄) + c'(S, {y}) + c'({x}, S̄)
                          = c(S, S̄) + ∂(Y ∩ S) + σ(X ∩ S̄)

**Skeleton** (for `(∃ f, IsFeasible σ dem f) ↔ ∀ S, ∂(Y ∩ Sᶜ) - σ(X ∩ Sᶜ) ≤ cap S`).
1. **Build `N'`** on `V ⊕ Unit ⊕ Unit`, with the super-source/super-sink arcs of
   capacities `σ`, `dem`.  ⚠ This is the same `N'` construction exercise 11.5.1
   needs and that the outline flags as missing; it must be built here.
2. **Feasibility ↔ saturating `(Y, {y})`** — exercise 11.5.1, deferred in this file
   (see its Book-statement block above).  Prove it as part of this theorem, or
   restore it as a lemma first.
3. **Such a flow is maximum**, by corollary 11.1, since its value is
   `∂(Y) = cap(Y, {y})`.
4. **Max-flow min-cut** (theorem 11.3) converts "a flow of value `∂(Y)` exists" into
   "every cut of `N'` has capacity `≥ ∂(Y)`".
5. **Expand the cut capacity** as in the book's display and cancel `∂(Y)`; the
   remaining inequality is literally (11.14).

**Reading.**  A feasible flow exists exactly when, for every way of splitting the
vertices, the capacity available for shipping into `S̄` covers the *net* demand there
— the demand of the sinks in `S̄` less whatever supply already sits inside `S̄`.
Necessity is obvious (that much material must cross the boundary); the content is
sufficiency.

**Formalisation.**  ⚠ Steps 3–4 use corollary 11.1 and theorem 11.3, both currently
false for want of the `N.X = {N.x}` link — though note `N'` is built with a genuine
single source and sink, so the repair is satisfied *there*; the defect bites only if
one tries to apply those results to `N` itself.  Step 1's construction is the
largest single piece of work in §11.5. -/
theorem gale_feasible_flow (N : Network V) (σ dem : V → ℕ) :
    (∃ f, N.IsFeasible σ dem f) ↔
      ∀ S : Finset V,
        ((∑ v ∈ (N.Y ∩ Sᶜ), dem v : ℤ)) - ((∑ v ∈ (N.X ∩ Sᶜ), σ v : ℤ))
          ≤ (N.capOf S : ℤ) := by
  sorry

-- Thm 11.9: Gale–Ryser realisability (Ryser, 1957) — the chapter's hardest item.
-- ⚠ suspected source typo in (11.19); the (0,1)-matrix carrier `B` is used (not `IsBipartiteWith`).
/-- **Theorem 11.9** (Gale–Ryser; Ryser, 1957).  *Let `p = (p₁, …, p_m)` and
`q = (q₁, …, q_n)` be sequences of non-negative integers satisfying
`∑ pᵢ = ∑ qⱼ` (11.16) and `q₁ ≥ q₂ ≥ … ≥ q_n` (11.17).  Then `(p, q)` is
realisable by a simple bipartite graph if and only if*

    ∑_{i=1}^{m} min{pᵢ, k} ≥ ∑_{j=1}^{k} qⱼ   for 1 ≤ k ≤ n.   (11.18)

**Book proof** (B&M §11.5, verbatim).  *Let `X = {x₁, …, x_m}` and `Y = {y₁, …, y_n}`
be two disjoint sets, and let `D` be the digraph obtained from the complete
bipartite graph with bipartition `(X, Y)` by orienting each edge from `X` to `Y`.
We obtain a network `N` by assigning unit capacity to each arc of `D` and
designating the vertices in `X` and `Y` as its sources and sinks, respectively.  We
shall assume, further, that the supply at source `xᵢ` is `pᵢ`, and that the demand
at sink `yⱼ` is `qⱼ`.*

*Now, to each spanning subgraph of `D`, there corresponds a flow in `N` which
saturates precisely the arcs of the subgraph, and this correspondence is clearly
one-one.  In view of (11.16), it follows that `(p, q)` is realisable by a simple
bipartite graph if and only if the network `N` has a feasible flow.  We now use
theorem 11.8.*

*For any set `S` of vertices in `N`, write `I(S) = {i | xᵢ ∈ S}` and
`J(S) = {j | yⱼ ∈ S}`.  Then, by definition,*

    c(S, S̄) = |I(S)| |J(S̄)|
    σ(X ∩ S̄) = ∑_{i ∈ I(S)} pᵢ   and   ∂(Y ∩ S̄) = ∑_{j ∈ J(S)} qⱼ    (11.19)

*Suppose that `N` has a feasible flow.  By theorem 11.8 and (11.19),
`|I(S)| |J(S̄)| ≥ ∑_{j ∈ J(S)} qⱼ - ∑_{i ∈ I(S)} pᵢ` for any `S ⊆ X ∪ Y`.  Setting
`S = {xᵢ | pᵢ > k} ∪ {yⱼ | j > k}`, we have
`∑_{i ∈ I(S)} min{pᵢ, k} ≥ ∑_{j=1}^{k} qⱼ - ∑_{i ∈ I(S)} min{pᵢ, k}`.  Since this
holds for all values of `k`, (11.18) follows.*

*Conversely, suppose that (11.18) is satisfied.  Let `S` be any set of vertices in
`N`.  By (11.18) and (11.19),
`c(S, S̄) ≥ ∑_{i ∈ I(S)} min{pᵢ, k} ≥ ∑_{j=1}^{k} qⱼ - ∑_{i ∈ I(S)} min{pᵢ, k} ≥ ∂(Y ∩ S̄) - σ(X ∩ S̄)`,
where `k = |J(S̄)|`.  It follows from theorem 11.8 that `N` has a feasible flow.*

⚠ **Suspected source typo in (11.19).**  As printed, `σ(X ∩ S̄)` and `∂(Y ∩ S̄)` are
given as sums over `I(S)` and `J(S)` — i.e. over `S`, not `S̄`.  For the
specialisation two paragraphs later to come out right, at least one of these must be
read with the complement.  Reconstruct (11.19) from the definitions rather than
transcribing it.

**Skeleton** (for `RealisableBipartite p q ↔ ∀ k, ∑_{j ≤ k} qⱼ ≤ ∑ᵢ min pᵢ (k+1)`).
1. **Build the bipartite network** of the book's first paragraph, on
   `Fin m ⊕ Fin n`, with unit capacities, `X = Fin m`, `Y = Fin n`, supplies `p`,
   demands `q`.
2. **Realisability ↔ feasibility.**  A `(0,1)`-matrix `B` ↔ a flow saturating
   exactly the arcs where `b_ij = 1`.  Row sums become resultant flows out of
   sources, column sums resultant flows in — so `B` realises `(p, q)` iff the flow
   is feasible.  ⚠ Here `hsum` (11.16) is spent: feasibility only bounds supplies
   above and demands below, and equality of the totals is what forces both to hold
   with equality.
3. **Apply theorem 11.8**, giving Gale's condition for all `S`.
4. **(⇒) Specialise** `S = {xᵢ | pᵢ > k} ∪ {yⱼ | j > k}` and simplify to (11.18).
5. **(⇐)** For arbitrary `S`, put `k := |J(S̄)|` and chain the book's three
   inequalities.  ⚠ `hmono` (11.17) is spent here — it is what makes "the `k`
   largest `q`'s" be `q₁, …, q_k`.

**Reading.**  Equal sums (11.16) are necessary — both count the edges — but not
sufficient, as `p = q = (5,4,4,2,1)` shows.  Condition (11.18) adds that the `k`
largest demands can actually be met: each `xᵢ` can supply at most `min{pᵢ, k}` of
them, having only `pᵢ` edges and only `k` targets.

*Matrix form.*  Let `B*` have its first `pᵢ` entries of row `i` equal to `1`, and let
`p*` be its column sums — the **conjugate** of `p` (that of `(5,4,4,2,1)` is
`(5,4,3,3,1)`).  Row `i` contributes `min{pᵢ, k}` to `∑_{j≤k} p*ⱼ`, so (11.18) says
exactly `∑_{j≤k} p*ⱼ ≥ ∑_{j≤k} qⱼ` — the conjugate of `p` dominates `q`.  Due to
Ryser (1957).

**Formalisation.**  The chapter's hardest item.  `k` is a `Fin n` and the book's
`1 ≤ k ≤ n` becomes `k.val + 1` in the `min`, so check the off-by-one against the
book when filling.  The `(0,1)`-matrix carrier is used rather than a bipartite-graph
predicate; see `RealisableBipartite`. -/
theorem galeRyser_realisable {m n : ℕ} (p : Fin m → ℕ) (q : Fin n → ℕ)
    (hsum : ∑ i, p i = ∑ j, q j)                          -- (11.16)
    (hmono : ∀ j j' : Fin n, j ≤ j' → q j' ≤ q j) :        -- (11.17)
    RealisableBipartite p q ↔
      ∀ k : Fin n, ∑ j ∈ Finset.univ.filter (· ≤ k), q j
                     ≤ ∑ i, min (p i) (k.val + 1) := by    -- (11.18)
  sorry

-- Ex 11.5.4(a)*: `(p,q)` realisable ⇔ the reduced pair `(p′,q′)` realisable.
-- NOTE: `p′` drops `p 0`; `q′` subtracts 1 from the first `p 0` entries (ℕ-truncated subtraction, per
-- the outline).  A candidate statement; the exact B&M `q′` re-sorts, elided here.
/-- **Exercise 11.5.4(a)***.  *Let `p` and `q` be nonincreasing sequences of
non-negative integers, and denote by `p'` the sequence `(p₂, …, p_m)` and by `q'`
the sequence `(q₁ - 1, …, q_{p₁} - 1, q_{p₁+1}, …, q_n)`.  Then `(p, q)` is
realisable by a simple bipartite graph if and only if the same is true of
`(p', q')`.*

**Book proof.**  None — an exercise, and one the book **stars**.

**Skeleton** (for `RealisableBipartite p q ↔ RealisableBipartite p' q'`).
1. **(⇐) is easy.**  Given a realisation `B'` of `(p', q')`, adjoin a new row `0`
   with ones in exactly the first `p 0` columns.  Its row sum is `p 0`; each of
   those columns gains one, restoring `q` from `q'`.
2. **(⇒) is the exchange argument.**  Given a realisation `B` of `(p, q)`, if row
   `0` is *not* supported on the first `p 0` columns, there are columns `j < j'`
   with `B 0 j = 0`, `B 0 j' = 1` and `q j ≥ q j'`.  Since `q j ≥ q j'`, some other
   row `i` has `B i j = 1`, `B i j' = 0`; swap the four entries.  Row sums and
   column sums are unchanged, and row `0` moves strictly closer to the greedy
   pattern.  Iterate — a decreasing measure (e.g. `∑ j * B 0 j`) terminates it.
3. Delete the now-greedy row `0`; the remaining matrix realises `(p', q')`.

**Reading.**  The bipartite analogue of the Havel–Hakimi reduction for degree
sequences (exercise 1.5.7): the vertex `x₁` may as well spend its `p₁` edges on the
`p₁` highest-demand vertices of `Y`.  Part (b) — dropped here as procedural — turns
this into a construction algorithm.

**Formalisation.**  ⚠ Two departures, both flagged in the source comment.  (i) `q'`
uses **truncated** natural subtraction (`q j - 1` is `0` when `q j = 0`), which is
harmless only because a realisable `q` has `q j ≥ 1` wherever row `0` puts an edge —
worth checking rather than assuming.  (ii) B&M's `q'` is **re-sorted** into
nonincreasing order, which this statement elides; without re-sorting, `q'` need not
satisfy (11.17), so this reduction cannot be chained with theorem 11.9 as the book
intends.  If the intent is to iterate the reduction, the re-sorting must be
restored. -/
theorem realisable_iff_reduced {m n : ℕ} (p : Fin (m + 1) → ℕ) (q : Fin n → ℕ) :
    RealisableBipartite p q ↔
      RealisableBipartite (fun i : Fin m => p i.succ)
        (fun j : Fin n => q j - (if (j : ℕ) < p 0 then 1 else 0)) := by
  sorry

-- Ex 11.5.4(b): DROPPED — "describe an algorithm" is procedural.

-- Ex 11.5.5(a)*: `(m,n)`-orientable ⇔ a partition condition. ⚠ needs an eulerian orientation (ch4/ch10).
/-- **Exercise 11.5.5(a)***.  *`G` is `(m,n)`-orientable if and only if there is a
partition `(V₁, V₂)` of `V` such that, for every `S ⊆ V`,*

    |(m - n)(|V₁ ∩ S| - |V₂ ∩ S|)| ≤ |[S, S̄]|.

**Book proof.**  None — an exercise, and one the book **stars**.

**Skeleton** (for `IsOrientable G m n ↔ ∃ V₁ V₂, partition ∧ ∀ S, the two-sided bound`).
1. **(⇒).**  Given an orientation, let `V₁` be the vertices of indegree `m` and `V₂`
   those of indegree `n`; that is a partition.  For any `S`, count arcs across
   `(S, Sᶜ)` in each direction: the prescribed indegrees fix the imbalance at
   `(m - n)(|V₁ ∩ S| - |V₂ ∩ S|)`, and it cannot exceed the number of edges
   available to carry it, `|[S, S̄]|`.  ⚠ The regularity `hreg` is spent here — it is
   what converts indegrees into a statement about the boundary.
2. **(⇐).**  Given the partition and the inequality, model the orientation as a flow
   problem: start from an **eulerian** orientation, in which every vertex is as
   balanced as possible, and use Gale's theorem 11.8 to decide that the required
   adjustment towards the prescribed indegrees is achievable — the inequality is
   exactly (11.14) for the associated network.

**Reading.**  An `(m+n)`-regular graph is to be oriented so every indegree is `m` or
`n`.  The partition names in advance which vertices get which, and the inequality is
a feasibility condition in Gale's sense.

**Formalisation.**  ⚠ Step 2 needs an **eulerian orientation**, which comes from
chapters 4 and 10 (every graph with all degrees even has an Euler tour; orient along
it) — a genuine import, absent from this file.  Note `(m+n)`-regular forces every
degree even only when `m + n` is even, so the eulerian step may itself need the
odd-degree patch of chapter 10's exercise 10.1.10.  The absolute value is written as
a **two-sided bound** to avoid `abs` and keep the arithmetic in `ℤ`. -/
theorem isOrientable_iff_exists_partition (G : SimpleGraph V) [DecidableRel G.Adj] (m n : ℕ)
    (hreg : G.IsRegularOfDegree (m + n)) :
    IsOrientable G m n ↔
      ∃ V₁ V₂ : Finset V, V₁ ∪ V₂ = Finset.univ ∧ Disjoint V₁ V₂ ∧
        -- `|(m-n)(|V₁∩S| - |V₂∩S|)| ≤ |[S,S̄]|`, written as a two-sided bound to avoid `abs`.
        ∀ S : Finset V,
          ((m : ℤ) - n) * (((V₁ ∩ S).card : ℤ) - ((V₂ ∩ S).card : ℤ)) ≤ (edgeBoundaryCard G S : ℤ) ∧
          -(edgeBoundaryCard G S : ℤ)
            ≤ ((m : ℤ) - n) * (((V₁ ∩ S).card : ℤ) - ((V₂ ∩ S).card : ℤ)) := by
  sorry

-- Ex 11.5.5(b): `(m,n)`-orientable and `m > n` ⇒ also `(m−1, n+1)`-orientable.
/-- **Exercise 11.5.5(b).**  *Deduce that if `G` is `(m,n)`-orientable and `m > n`,
then `G` is also `(m-1, n+1)`-orientable.*

**Book proof.**  None — an exercise; "deduce" points at part (a).

**Skeleton** (for `IsOrientable G (m-1) (n+1)`, given `IsOrientable G m n` and `n < m`).
1. Part (a) on `h` gives a partition `(V₁, V₂)` satisfying the bound with
   coefficient `m - n`.
2. **The same partition works for `(m-1, n+1)`.**  The coefficient becomes
   `(m-1) - (n+1) = m - n - 2`, which is smaller in absolute value (using
   `hmn : n < m`, so `m - n ≥ 1`), while `|[S, S̄]|` is unchanged.  So the two-sided
   bound still holds — each side scales down.
3. **Regularity is preserved**: `(m-1) + (n+1) = m + n`, so `hreg` transfers
   unchanged.  ⚠ In `ℕ`, `m - 1` needs `1 ≤ m`, which `hmn` supplies.
4. Part (a) in the `⇐` direction gives `IsOrientable G (m-1) (n+1)`.

**Reading.**  The two permitted indegrees can always be moved one step closer
together.  Iterating, an `(m,n)`-orientable graph is `(m',n')`-orientable for every
admissible pair with `m' + n' = m + n` and `|m' - n'| ≤ |m - n|` — in particular the
most balanced orientation is always available.

**Formalisation.**  A short deduction *given* part (a), which is the starred and
substantial half.  Step 2's "scales down" should be checked at the sign: the bound
is two-sided, so both directions shrink only because `|m - n - 2| ≤ |m - n|` when
`m - n ≥ 1`. -/
theorem isOrientable_pred_succ (G : SimpleGraph V) [DecidableRel G.Adj] (m n : ℕ)
    (hreg : G.IsRegularOfDegree (m + n)) (hmn : n < m) (h : IsOrientable G m n) :
    IsOrientable G (m - 1) (n + 1) := by
  sorry

/-!
## Dropped / N/A items (recorded, not stated)

* **Ex 11.1.1, Ex 11.2.1, Ex 11.3.2** — `[figure omitted]` in the source; unstatable.
* **Ex 11.3.2, Ex 11.3.4, Ex 11.3.5\*** — "use/modify the labelling method"; procedural.
* **Ex 11.3.3** — vacuous under B&M's integer-valued flows (faithful ℝ-form is a second carrier).
* **Ex 11.4.2** — derive König from Thm 11.7; an alternative derivation of ch5's Thm 5.3, not new.
* **Ex 11.5.3** — "find necessary and sufficient conditions"; no proposition stated.
* **Ex 11.5.4(b)** — "describe an algorithm"; procedural.
* The labelling method / procedure / scan / breakthrough, the `f`-unsaturated tree, and the
  Edmonds–Karp complexity claim — procedural / proof-only; no theorem attached.

### Book content for these items

*Exercise 11.1.1, 11.2.1, 11.3.2.*  Determine all flows / all cuts / apply the
labelling method to specific networks given only as figures.

*Exercise 11.3.3 (integrality).*  In any network with integer capacities there is a
maximum flow `f` with `f(a)` an integer for every arc.  This is immediate from the
labelling method, which only ever adds or subtracts the integer `ι(P)`; it is
vacuous under the book's convention that flows are integer-valued to begin with,
and the faithful `ℝ`-valued statement would need a second carrier.

*Exercise 11.3.4.*  With a lower bound `b(a) ≤ c(a)` on each arc, modify the
labelling method to find a maximum flow subject to `f(a) ≥ b(a)`.

*Exercise 11.3.5*.*  With a capacity `m(v)` on each intermediate vertex, find a
maximum flow satisfying `f⁻(v) ≤ m(v)` by applying the labelling method to a
modified network — split each vertex as in theorem 11.6 and give the internal arc
capacity `m(v)`.

*Exercise 11.4.2.*  Derive König's theorem (5.3) from theorem 11.7.

*Exercise 11.5.3.*  Find necessary and sufficient conditions on `p`, `q` for a
digraph with `d⁻(vᵢ) = pᵢ`, `d⁺(vᵢ) = qᵢ` and a `(0,1)` adjacency matrix.

*The labelling method (§11.3).*  A tree `T` is **`f`-unsaturated** when `x ∈ V(T)`
and the unique `(x, v)`-path in `T` is `f`-unsaturated for every `v ∈ T`.  Grow it
by adjoining (1) an `f`-unsaturated arc out of `V(T)` together with its head, or
(2) an `f`-positive arc into `V(T)` together with its tail.  Label `x` with `∞`
and each new vertex `v` with `l(v) = min{l(u), c(a) - f(a)}` or
`min{l(u), f(a)}` respectively, so `l(v) = ι(P_v)`.  **Breakthrough** is when `y`
gets labelled — the `(x, y)`-path is then `f`-incrementing with known `ι`.  If
instead all labelled vertices are scanned without reaching `y`, theorem 11.1 and
corollary 11.1 certify `f` maximum.  Ford and Fulkerson (1957); made good by
Edmonds and Karp (1970) via first-labelled-first-scanned, i.e. shortest
incrementing paths.
-/

end Networks
