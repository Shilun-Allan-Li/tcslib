import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Bondy & Murty, *Graph Theory with Applications* — Chapter 12: The Cycle Space and Bond Space

Sorry-skeleton extracted from `papers/bondy-murty-ch12-cycle-bond-space.md`.

Every proof body is `sorry`; this file is a scaffold for sorry-driven development
(fill one stub at a time, `lake build` after each).

## Carrier decisions (from the outline)
* B&M ch12 is the **oriented, real** cycle space on a **digraph** — NOT the GF(2) theory.
  A digraph is encoded by two functions `tail head : A → V` (arcs `A`, vertices `V`), which
  supports loops (`tail a = head a`) and parallel arcs (`Mathlib`'s `Digraph` cannot).
* The chapter is stated over a general `[Field F]` (so Ex 12.1.5 is subsumed); §12.2's
  integer-determinant results live over `ℤ`.
* Orthogonality uses `LinearMap.BilinForm.orthogonal` on `A → F` with the dot form
  (NOT `Submodule.orthogonal`/`ᗮ`, which needs `RCLike` and dies over `ZMod p`).

The `import TCSlib.*` lines from the outline are dropped (those repo files do not exist).

## How each declaration is annotated

Every docstring below has a fixed shape, so the book's mathematics stays separable
from this file's formalisation choices:

1. **The book's own statement** (theorem) or **definition** (`def`), quoted verbatim
   from Bondy & Murty, LaTeX transcribed into Lean-style backticks.
2. **Book proof** — B&M's printed proof, verbatim.  Chapter 12 proves theorems
   12.1–12.4, lemmas 12.2.1/12.2.2 and corollaries 12.2/12.4; everything else is an
   exercise or extracted from prose, and says so.
3. **Skeleton** — an *abstract* numbered plan keyed to the Lean statement, naming
   intermediate facts, not committing to tactics.
4. **Reading** — what the result means and how it sits in the chapter.
5. **Formalisation** — only where the Lean statement departs from the book's.

Definitions carry parts 1, 4 and 5 only.

## ⚠ Nine definitions in this file are defective

A `sorry`-ed *proof* is an honest debt; a `sorry`-ed *definition* is an opaque
constant, so every statement mentioning it is vacuous — it typechecks but asserts
nothing.  Eight definitions here have `sorry` bodies, and a ninth is degenerate.
The damage is extensive enough to be worth tabulating:

* **`IsSpanningTree`** (`sorry`).  `tau` is defined by counting the `Finset`s
  satisfying it, so **`τ(G)` is an opaque natural number** and *every* §12.2 result
  is vacuous: theorem 12.4, (12.8), corollary 12.4, the matrix-tree theorem, and
  exercises 12.2.1(b), 12.2.2(b), 12.2.4(a) and (b).
* **`IsBasisMatrixOfTree`, `IsBasisMatrixOfTree'`** (`sorry`).  These are the
  hypotheses of theorems 12.3, 12.4, (12.8), corollary 12.4 and exercises 12.2.1(b),
  12.2.3(a), 12.2.4(a) — so those statements constrain nothing.
* **`IsMaximalForest`, `fundamentalCycle`, `fundamentalBondVertexSet`,
  `cycleCirculation`** (`sorry`).  These make the two tree-basis theorems
  (`isBasisMatrix_cycleSpace_of_maximalForest`,
  `isBasisMatrix_bondSpace_of_maximalForest`) vacuous.
* **`IsConnectedDigraph`** (`sorry`).  Hypothesis of the matrix-tree theorem and of
  exercise 12.1.3.
* **`ArcCycle` is degenerate** — not `sorry`, but worse, because it looks honest.
  It carries only `arcs : List A` and `nonempty : arcs ≠ []`, with **no closed-walk
  or distinctness conditions** (the docstring calls them "elided").  Consequently
  *any* nonempty list of arcs is an "arc cycle", and

      IsArcAcyclic tail head S  ↔  S = ∅

  — for nonempty `S` pick `a ∈ S` and take the one-element list `[a]`.  So theorem
  12.2(i) currently reads *"the columns of `B | S` are independent iff `S = ∅`"*,
  which is false, and lemma 12.2.1 is trivially true for the wrong reason.

Nothing in §12.2 is meaningful until `ArcCycle`, `IsSpanningTree` and the two
`IsBasisMatrixOfTree` predicates are given honest bodies.  Per-declaration repairs
are in the individual docstrings.

## Dropped / subsumed items (see outline §Scope note and judgement 5)
* **Ex 12.1.1(a)** — figure omitted from source; unstatable.
* **Ex 12.1.4**, **Ex 12.3.2** — plane graphs / plane duals; planarity absent from Mathlib.
* **Ex 12.3.1**, **Ex 12.3.3\*** — squared-rectangle / 3D dissection theory absent.
* **Ex 12.1.5** — N/A: subsumed by stating §12.1 over `[Field F]` (this *is* Theorem 12.2).
* **Cauchy–Binet (12.7)** — its faithful *statement* cannot elaborate cleanly (the square
  submatrix is indexed by a subtype of size `card ι`, not by `ι`, so `det` is ill-typed
  without a per-subset equiv). Left as `-- TODO`. Theorem 12.4 is stated directly.
-/

namespace Matrix

/-- B&M's **unimodular** (Thm 12.3, p. 226): every *full* square submatrix (order `ν−1`,
selected by an injective column map) has determinant `0`, `+1` or `-1`.
⚠ NOT `Matrix.IsTotallyUnimodular`, which quantifies over *all* square submatrices — that is
B&M's *totally* unimodular (Ex 12.2.3), a strictly stronger property.

**Book definition** (B&M §12.2, verbatim).  *A matrix is said to be unimodular if all
its full square submatrices have determinants `0`, `+1` or `-1`.*

**Reading.**  "Full" means as large as the matrix allows — for a `(ν-1) × ε` basis
matrix of the bond space, the square submatrices of order `ν - 1`.  Theorem 12.3
says such a basis matrix is unimodular, and that is exactly what makes theorem
12.4's determinant count the spanning trees: each nonsingular full submatrix
contributes `(±1)² = 1`.

**Formalisation.**  ⚠ **Not** `Matrix.IsTotallyUnimodular`, which quantifies over
*all* square submatrices — that is B&M's strictly stronger *totally* unimodular of
exercise 12.2.3, stated separately below.  "Full square submatrix" is rendered as
`M.submatrix id g` for an injective `g : n → m`: all rows, and `card n` columns
chosen injectively.  Placed in the `Matrix` namespace so it reads
`B.IsUnimodular`. -/
def IsUnimodular {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (M : Matrix n m ℤ) : Prop :=
  ∀ g : n → m, Function.Injective g → (M.submatrix id g).det ∈ ({0, 1, -1} : Set ℤ)

end Matrix

namespace CycleSpace

open scoped Matrix

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {F : Type*} [Field F]
variable (tail head : A → V)
variable {n : Type*} [Fintype n]

/-! ## Key Definitions -/

/-- B&M's **oriented incidence matrix** `M` (p. 222). ⚠ MISSING from Mathlib:
`SimpleGraph.incMatrix` is the UNORIENTED 0/1 matrix; the oriented version is Mathlib's own
open TODO. B&M's "if `a` is a link" clause (loops ↦ 0) is automatic: a loop has
`tail a = head a = v`, giving `1 - 1 = 0`.

**Book definition** (B&M §12.1, verbatim).  *With each vertex `v` of `D` we associate
the function `m_v` on `A` defined by*

    m_v(a) = 1   if a is a link and v is the tail of a
           = -1  if a is a link and v is the head of a
           = 0   otherwise

*The incidence matrix of `D` is the matrix `M` whose rows are the functions `m_v`.*

**Reading.**  Record, for each vertex and each arc, whether the arc leaves the
vertex (`+1`), enters it (`-1`), or misses it (`0`).  The signs make this the
*oriented* incidence matrix, distinct from the `0/1` matrix of §1.3, and they encode
the conservation condition exactly: `M *ᵥ f = 0` says inflow balances outflow at
every vertex.

**Formalisation.**  ⚠ Missing from Mathlib: `SimpleGraph.incMatrix` is the
*unoriented* `0/1` matrix, and the oriented version is one of Mathlib's own open
TODOs.  B&M's "if `a` is a link" clause (i.e. loops map to `0`) is **automatic** in
this encoding: a loop has `tail a = head a = v`, so the two indicators cancel to
`1 - 1 = 0`.  Stated over a general `[Ring R]` so the same definition serves the
`F`-valued §12.1 and the `ℤ`-valued §12.2. -/
def orientedIncMatrix (R : Type*) [Ring R] : Matrix V A R :=
  Matrix.of fun v a => (if tail a = v then 1 else 0) - (if head a = v then 1 else 0)

/-- The **cycle space** `𝓒`: circulations, i.e. `M *ᵥ f = 0`, B&M's (12.1).

**Book definition** (B&M §12.1, verbatim).  *Let `D` be a digraph.  A real-valued
function `f` on `A` is called a circulation in `D` if it satisfies the conservation
condition at each vertex:*

    f⁻(v) = f⁺(v)   for all v ∈ V                                    (12.1)

*If we think of `D` as an electrical network, then such a function `f` represents a
circulation of currents in `D`.  …  Thus the set of all circulations in `D` is a
vector space.  We denote this space by `𝓒`.  …  We shall see later on that each
circulation is a linear combination of the circulations associated with cycles.  For
this reason we refer to `𝓒` as the cycle space of `D`.*

**Reading.**  Currents that flow round and round without accumulating anywhere.
⚠ Contrast chapter 11, where conservation was imposed only at *intermediate*
vertices; here it holds **everywhere**, so there is no net source or sink.

**Formalisation.**  The conservation condition (12.1) is packaged as
`M *ᵥ f = 0`, i.e. `f ∈ ker M.mulVecLin` — theorem 12.1's second half is precisely
the claim that this repackaging is faithful.  Defining `𝓒` as a `Submodule`
directly gives the vector-space structure the book verifies by hand. -/
def cycleSpace : Submodule F (A → F) :=
  LinearMap.ker (orientedIncMatrix tail head F).mulVecLin

/-- The **bond space** `𝓑`: potential differences, i.e. `g = Mᵀ *ᵥ p`, B&M's (12.2).

**Book definition** (B&M §12.1, verbatim).  *Given a function `p` on the vertex set
`V` of `D`, we define the function `δp` on the arc set `A` by the rule that, if an
arc `a` has tail `x` and head `y`, then*

    δp(a) = p(x) - p(y)                                              (12.2)

*If `D` is thought of as an electrical network with potential `p(v)` at `v`, then,
by (12.2), `δp` represents the potential difference along the wires of the network.
For this reason a function `g` on `A` is called a potential difference in `D` if
`g = δp` for some function `p` on `V`.  …  the set `𝓑` of all potential differences
in `D` is a vector space.  …  We shall see that each potential difference is a
linear combination of potential differences associated with bonds.  For this reason
we refer to `𝓑` as the bond space of `D`.*

**Reading.**  Assign a voltage to every vertex and read off the drop across every
wire.  Theorem 12.1 identifies `𝓑` as the row space of `M` and `𝓒` as its
orthogonal complement — the duality organising the whole chapter.

**Formalisation.**  `δp` is `Mᵀ *ᵥ p`, so `𝓑` is the *range* of that map.  ⚠ Note
the asymmetry with `cycleSpace`: `𝓒` is a **kernel** and `𝓑` a **range**, which is
why theorem 12.2(ii) is a genuinely separate argument rather than a formal dual of
(i). -/
def bondSpace : Submodule F (A → F) :=
  LinearMap.range (orientedIncMatrix tail head F)ᵀ.mulVecLin

/-- The standard dot-product bilinear form on `K → K` (here `A → F`).
⚠ NOT an inner product — used with `LinearMap.BilinForm.orthogonal`, which works over every
field (in particular `ZMod p`), unlike `Submodule.orthogonal`/`ᗮ`. Body deferred.

**Book usage** (B&M §12.1).  Theorem 12.1 says `𝓒` is the **orthogonal complement**
of `𝓑`, orthogonality being with respect to the ordinary dot product on functions
`A → F`.

**Reading.**  `f` and `g` are orthogonal when `∑_{a ∈ A} f(a)g(a) = 0`.  For real
coefficients this is the usual inner product; but the chapter also needs it over
fields of characteristic `p` (exercise 12.2.4), where the form is **degenerate** and
a vector can be orthogonal to itself.  That degeneracy is precisely why Shank's
result — `dim(𝓑_F ∩ 𝓒_F) > 0` iff `p ∣ τ(G)` — is possible at all: over `ℝ` the two
spaces meet only in zero.

**Formalisation.**  ⚠ **Not** an inner product, and deliberately so.  Used with
`LinearMap.BilinForm.orthogonal`, which works over every field — in particular
`ZMod p` — unlike `Submodule.orthogonal`/`ᗮ`, which needs `RCLike` and would make
exercise 12.2.4 unstateable.  The four `mk₂` obligations are bilinearity, all
discharged by `simp` on sums. -/
def dotForm (K ι : Type*) [Field K] [Fintype ι] :
    LinearMap.BilinForm K (ι → K) :=
  LinearMap.mk₂ K (fun x y => ∑ i, x i * y i)
    (fun _ _ _ => by simp [add_mul, Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum, mul_assoc])
    (fun _ _ _ => by simp [mul_add, Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum, mul_left_comm])

@[simp]
theorem dotForm_apply {K ι : Type*} [Field K] [Fintype ι] (x y : ι → K) :
    dotForm K ι x y = ∑ i, x i * y i := rfl

/-- `G` is the underlying (simple) graph of the digraph `(tail, head)`.

**Book convention** (B&M §10.1, used throughout ch12).  The **underlying graph** of a
digraph is obtained by forgetting the direction of every arc.

**Reading.**  `u` and `v` are adjacent in `G` exactly when some arc runs between them
in one direction or the other.  The chapter's counting results — `dim 𝓑 = ν - ω`,
`dim 𝓒 = ε - ν + ω`, `τ(G)` — are all statements about this underlying graph, the
orientation being an auxiliary device that cancels out.

**Formalisation.**  ⚠ A `SimpleGraph` underlying graph loses information the arc
carrier has: loops (`tail a = head a`) and parallel arcs both vanish.  That is
harmless for the *counting* results, which are about `G`, but means `G` does not
determine `(tail, head)` — hence this is a relation, not a function. -/
def IsUnderlyingGraph (G : SimpleGraph V) : Prop :=
  ∀ u v : V, G.Adj u v ↔ (∃ a : A, (tail a = u ∧ head a = v) ∨ (tail a = v ∧ head a = u))

/-- `(tail, head)` is an orientation of the simple graph `G`.

**Book usage** (B&M §12.2, verbatim).  *Consider an arbitrary orientation `D` of
`G`…*

**Reading.**  `G` is recovered by forgetting directions.  The point of §12.2 is that
`τ(G)` is an invariant of `G` alone, yet is most easily computed through the
*oriented* incidence matrix of an arbitrarily chosen orientation — the signs cancel
in the determinant, which is exactly what exercise 12.2.2(a) makes precise.

**Formalisation.**  ⚠ Definitionally equal to `IsUnderlyingGraph`, so "orientation
of `G`" here means only "has `G` as underlying graph" — it does **not** forbid `D`
from having both `(u,v)` and `(v,u)`, which chapter 10's `IsOrientationOf` does.
For this chapter that is deliberate and harmless: the results are about `M` and
`MMᵀ`, which tolerate digons and loops. -/
def IsOrientationOf (G : SimpleGraph V) : Prop := IsUnderlyingGraph tail head G

/-- The digraph `(tail, head)` is connected. Structural predicate; body deferred.

**Book usage** (B&M exercise 12.1.3, §12.2).  Connectivity of the underlying graph
is what makes `ω = 1`, so that `dim 𝓑 = ν - 1` and deleting a single row of the
incidence matrix leaves a basis matrix of the bond space.

**⚠ Defective: `sorry` body.**  `IsConnectedDigraph` is an opaque proposition, so the
matrix-tree theorem and exercise 12.1.3 — the two statements taking it as a
hypothesis — constrain nothing.

*The repair* is one line: connectivity of the **underlying graph**, which is what
B&M mean (§10.1: every concept valid for graphs applies to digraphs via the
underlying graph).  E.g.

    IsConnectedDigraph tail head :=
      ∀ u v : V, Relation.ReflTransGen (fun x y => ∃ a, (tail a = x ∧ head a = y) ∨
                                                        (tail a = y ∧ head a = x)) u v

— reachability ignoring arc direction, plus `Nonempty V` if the empty digraph should
be excluded.  Nothing here needs a path API. -/
def IsConnectedDigraph (tail head : A → V) : Prop := sorry

/-- An **arc-level cycle** in the digraph, as a nonempty closed arc-sequence.
⚠ `SimpleGraph.Walk.IsCycle` is unusable here: it cannot express B&M's loops or digons.
Only the minimal shape is recorded; the closed/interior-distinct invariants are elided.

**Book usage** (B&M §12.1, verbatim).  *Let `C` be a cycle in `D` with an assigned
orientation and let `C⁺` denote the set of arcs of `C` whose direction agrees with
this orientation.*

**Reading.**  A cycle of the *underlying* graph, traversed in one of its two
directions; some arcs point along the direction of travel and some against it,
which is what the sign in `f_C` records.

**⚠ Defective: this structure is degenerate.**  It carries only a nonempty list of
arcs, with **no** closed-walk condition and **no** distinctness condition — the
docstring's "the closed/interior-distinct invariants are elided" understates the
cost.  As a result *any* nonempty list of arcs is an `ArcCycle`, and the derived
predicate collapses:

    IsArcAcyclic tail head S  ↔  S = ∅

(for nonempty `S`, pick `a ∈ S` and take the one-element list `[a]`).  Downstream,
theorem 12.2(i) then reads *"the columns of `B | S` are independent iff `S = ∅`"* —
false — and lemma 12.2.1 becomes trivially true for the wrong reason.  This is not
`sorry`, which makes it more dangerous: the definition *looks* honest.

*The repair* needs three fields beyond `arcs` and `nonempty`:
* **closed walk** — a vertex sequence `verts : List V` with `verts.length = arcs.length`
  such that consecutive arcs meet head-to-tail, cyclically: for each `i`,
  `{tail arcs[i], head arcs[i]} = {verts[i], verts[i+1 mod n]}` (the set form allows
  an arc to be traversed against its direction, which is exactly what `C⁺` records);
* **interior distinctness** — `verts.Nodup`;
* optionally **no repeated arc** — `arcs.Nodup`.

⚠ `SimpleGraph.Walk.IsCycle` genuinely cannot serve, as the note says: the chapter's
digraphs admit loops (`tail a = head a`) and parallel arcs, which a `SimpleGraph`
cannot express.  But that argues for building the structure properly, not for
omitting its invariants. -/
structure ArcCycle (tail head : A → V) where
  arcs : List A
  nonempty : arcs ≠ []

/-- `S ⊆ A` is **acyclic**: it contains no arc-cycle.

**Book usage** (B&M theorem 12.2, verbatim).  *…the columns of `B | S` are linearly
independent if and only if `S` is acyclic.*

**Reading.**  No cycle of the digraph lies entirely inside `S`.  Theorem 12.2 makes
this combinatorial property equivalent to a linear-algebraic one — the bridge that
turns counting spanning trees into counting nonsingular submatrices.

**⚠ Defective by inheritance.**  Because `ArcCycle` has no closure or distinctness
conditions, this predicate collapses to `S = ∅`; see `ArcCycle`'s docstring for the
one-line argument and the repair.  The definition here is *correct given a correct
`ArcCycle`* — nothing needs changing at this declaration. -/
def IsArcAcyclic (tail head : A → V) (S : Finset A) : Prop :=
  ¬ ∃ c : ArcCycle tail head, ∀ a ∈ c.arcs, a ∈ S

/-- `f_C`: the circulation of an oriented cycle (`±1` on `C⁺ / C⁻`, `0` off `C`). Body deferred
(it depends on the concrete `ArcCycle` orientation).

**Book definition** (B&M §12.1, verbatim).  *We associate with `C` the function `f_C`
defined by*

    f_C(a) = 1   if a ∈ C⁺
           = -1  if a ∈ C \ C⁺
           = 0   if a ∉ C

*Clearly, `f_C` satisfies (12.1) and hence is a circulation.*

**Reading.**  Send one unit of current round the cycle in the chosen direction; arcs
pointing with the flow carry `+1`, those against it `-1`, everything else nothing.
Conservation holds at every vertex because the cycle enters and leaves each of its
vertices exactly once.  These are the elementary circulations from which all others
are built, and they give the cycle space its name.

**⚠ Defective: `sorry` body.**  `f_C` is an opaque function, so
`isBasisMatrix_cycleSpace_of_maximalForest` — whose rows are these — asserts nothing.

*The repair* depends on repairing `ArcCycle` first: once a cycle carries its vertex
sequence, `C⁺` is definable (arc `i` is in `C⁺` when `tail arcs[i] = verts[i]`, i.e.
it is traversed forwards), and

    f_C a = if a ∉ arcs then 0 else if a ∈ C⁺ then 1 else -1

⚠ With `arcs` a `List`, `a ∈ C⁺` needs the *position*, not just membership — an arc
could in principle occur twice.  Adding `arcs.Nodup` to `ArcCycle` removes that
ambiguity and is the cleaner route. -/
def cycleCirculation (tail head : A → V) (c : ArcCycle tail head) : A → F := sorry

/-- B&M's edge cut `[S, S̄]`: the arcs with exactly one end in `S`.

**Book definition** (B&M §2.2, used throughout ch12).  `[S, S̄]` is the set of edges
with one end in `S` and the other outside.

**Reading.**  The arcs crossing the boundary of `S`, in either direction.  The
*direction* matters for the associated potential difference `g_B`, which takes `+1`
on arcs leaving `S` and `-1` on those entering it — the edge cut is undirected, its
potential difference is not.

**Formalisation.**  A `Set A`, not a `Finset`, matching `IsBond`'s quantification
over arbitrary `S : Set V`. -/
def edgeCutSet (S : Set V) : Set A :=
  {a | (tail a ∈ S ∧ head a ∉ S) ∨ (tail a ∉ S ∧ head a ∈ S)}

/-- A **bond**: a MINIMAL nonempty edge cut.
⚠ MISSING from Mathlib. `Dart.lean` calls a dart a "bond" — an unrelated half-edge notion.
The repo's `IsEdgeCut` is a *cut*, not a *bond* (no minimality), and on the wrong carrier.

**Book definition** (B&M §2.2, verbatim).  *A minimal nonempty edge cut of `G` is
called a bond.*

**Reading.**  An edge cut with nothing to spare.  Bonds are dual to cycles: lemma
12.2.2 says the support of a nonzero potential difference contains a bond, exactly
as lemma 12.2.1 says the support of a nonzero circulation contains a cycle.

**Formalisation.**  ⚠ Missing from Mathlib — and beware two false friends.
`Dart.lean` uses "bond" for an unrelated half-edge notion, and the repo's
`IsEdgeCut` is a *cut* without the minimality clause, on a different carrier.

⚠ The minimality clause here quantifies over subsets `B' ⊆ B` that are **themselves
edge cuts** (`∃ S', B' = edgeCutSet S'`).  That is the right reading of "minimal
nonempty edge cut" and is stronger than minimality among arbitrary subsets; check it
against use sites, since lemma 12.2.2 only produces an edge cut inside the support
and then needs a *bond* inside that. -/
def IsBond (tail head : A → V) (B : Set A) : Prop :=
  (∃ S : Set V, B = edgeCutSet tail head S) ∧ B.Nonempty ∧
    ∀ B' ⊆ B, B'.Nonempty → (∃ S : Set V, B' = edgeCutSet tail head S) → B' = B

open scoped Classical in
/-- `g_B`: the potential difference of a bond, `p = ` indicator of `S` (B&M give it, p. 221).

**Book definition** (B&M §12.1, verbatim).  *Let `B = [S, S̄]` be a bond of `D`.  We
define `g_B` by*

    g_B(a) = 1   if a ∈ (S, S̄)
           = -1  if a ∈ (S̄, S)
           = 0   if a ∉ B

*It can be verified that `g_B = δp` where `p(v) = 1` if `v ∈ S` and `0` if
`v ∈ S̄`.*

**Reading.**  Put every vertex of `S` at voltage `1` and every other at `0`; the
drops are `+1` on arcs leaving `S`, `-1` on arcs entering, `0` on arcs with both
ends on one side.  These are the elementary potential differences, and they give the
bond space its name.

**Formalisation.**  Defined directly by the book's `δp` formula with `p` the
indicator of `S`, rather than by the three-case rule — that makes membership in `𝓑`
immediate and turns the book's "it can be verified" into `rfl`.  Note the definition
takes an arbitrary `S : Set V`, not a bond, so `g_B` exists for any vertex set; the
bond condition matters only for the *basis* claims. -/
noncomputable def bondPotentialDiff (tail head : A → V) (S : Set V) : A → F :=
  fun a => (if tail a ∈ S then (1 : F) else 0) - (if head a ∈ S then 1 else 0)

/-- A **basis matrix** of a submodule `W ≤ (A → F)`: its rows are a basis of `W`.

**Book definition** (B&M §12.1, verbatim).  *A matrix `B` is called a basis matrix of
`𝓑` if the rows of `B` form a basis for `𝓑`; a basis matrix of `𝓒` is similarly
defined.*

**Reading.**  Package a basis as the rows of a matrix, so questions about the space
become questions about the matrix.  This is what lets theorem 12.2 phrase acyclicity
as linear independence of *columns*, and theorem 12.4 count spanning trees by a
determinant.

**Formalisation.**  "Rows form a basis" is unfolded into its two halves —
`LinearIndependent F M` and `span (range M) = W` — rather than using `Basis`, which
would require a chosen index equivalence.  The row index `n` is a free `Fintype`,
so the same predicate serves matrices indexed by `T`, by `Tᶜ`, or by `{v // v ≠ y}`. -/
def IsBasisMatrix (M : Matrix n A F) (W : Submodule F (A → F)) : Prop :=
  LinearIndependent F M ∧ Submodule.span F (Set.range M) = W

/-- `M | S` — B&M's column restriction (`Matrix.submatrix`).

**Book notation (§12.1).**  *If `R` is a matrix whose columns are labelled with
the elements of `A`, and if `S ⊆ A`, we shall denote by `R | S` the submatrix of
`R` consisting of those columns labelled with elements in `S`.  If `R` has a
single row, our notation is the same as the usual notation for the restriction of
a function to a subset of its domain.* -/
abbrev restrictCols (M : Matrix n A F) (S : Finset A) : Matrix n {a // a ∈ S} F :=
  M.submatrix id Subtype.val

/-- A **spanning tree** of the digraph. Structural predicate; body deferred.

**Book definition** (B&M §2.2).  A spanning subgraph that is a tree.

**Reading.**  A maximal acyclic set of arcs touching every vertex.  By theorem 12.2,
spanning trees are exactly the `(ν-1)`-element subsets `S` for which `B | S` is
nonsingular — which is what makes §12.2's determinant formula count them.

**⚠ Defective: `sorry` body — the most damaging one in the file.**  `tau` counts the
`Finset`s satisfying this predicate, so **`τ(G)` is an opaque natural number**, and
every §12.2 statement about it is vacuous: theorem 12.4, (12.8), corollary 12.4, the
matrix-tree theorem, and exercises 12.2.1(b), 12.2.2(b), 12.2.4(a), (b).

*The repair*, once `ArcCycle` is fixed:

    IsSpanningTree tail head T := IsArcAcyclic tail head T ∧ T.card + 1 = Fintype.card V
                                  ∧ (the underlying subgraph on T is connected)

or equivalently "acyclic and spanning", using the connectivity notion suggested for
`IsConnectedDigraph`.  Acyclic plus `|T| = ν - 1` already forces connectivity for a
graph on `ν` vertices, so the middle clause plus acyclicity suffices — but only once
`IsArcAcyclic` is genuine. -/
def IsSpanningTree (tail head : A → V) (T : Finset A) : Prop := sorry

/-- A **maximal forest** of the digraph. Structural predicate; body deferred.

**Book usage** (B&M corollary 12.2, verbatim).  *The above maximum is attained when
`S` is a maximal forest of `D`, and is therefore (exercise 2.2.4) equal to `ν - ω`.*

**Reading.**  A maximal acyclic set of arcs — a spanning tree of each component.
Its size `ν - ω` is exactly the rank of the bond space, which is how corollary 12.2
computes `dim 𝓑`.

**⚠ Defective: `sorry` body.**  Makes both tree-basis theorems
(`isBasisMatrix_cycleSpace_of_maximalForest`,
`isBasisMatrix_bondSpace_of_maximalForest`) vacuous, and is a hypothesis of
`fundamentalCycle`.

*The repair:* `IsArcAcyclic tail head T ∧ ∀ a ∉ T, ¬ IsArcAcyclic tail head (insert a T)`
— acyclic and maximally so.  Note this is the *forest* notion, weaker than
`IsSpanningTree`: it does not require connectivity, which is exactly why corollary
12.2 gets `ν - ω` rather than `ν - 1`. -/
def IsMaximalForest (tail head : A → V) (T : Finset A) : Prop := sorry

/-- The **fundamental cycle** of `a ∉ T` (`T + a` contains a unique cycle). Body deferred;
lever: `IsAcyclic.path_unique`.

**Book definition** (B&M §12.1, p. 224, verbatim).  *Let `T` be a maximal forest of
`D`.  Associated with `T` is a special basis matrix of `𝓒`.  If `a` is an arc of
`T̄`, then `T + a` contains a unique cycle.  Let `C_a` denote this cycle and let
`f_a` denote the circulation corresponding to `C_a`, defined so that `f_a(a) = 1`.*

**Reading.**  The tree already provides a unique route between the ends of `a`
(theorem 2.1), and adding `a` closes exactly one cycle.  The `ε - ν + ω` fundamental
cycles, one per non-tree arc, give the tree-basis of the cycle space — the matrix
`C` is a basis matrix because `C | T̄` is an identity matrix, so its rank is full.

**⚠ Defective: `sorry` body.**  An opaque `ArcCycle`, so
`isBasisMatrix_cycleSpace_of_maximalForest` asserts nothing about it.

*The repair.*  The lever noted in the source comment is right: `IsAcyclic.path_unique`
gives the unique `T`-path between `a`'s ends, and the cycle is that path closed by
`a`.  ⚠ But it is stated for `SimpleGraph`, while this chapter's carrier is
`tail, head : A → V` with loops and parallel arcs — so either transfer along the
underlying graph (losing the multi-arc case) or redo the uniqueness argument on the
arc carrier.  The `hT` hypothesis is what makes "unique" true, and `ha : a ∉ T` what
makes the cycle exist. -/
def fundamentalCycle (tail head : A → V) (T : Finset A) (hT : IsMaximalForest tail head T)
    {a : A} (ha : a ∉ T) : ArcCycle tail head := sorry

/-- The vertex set `S` of the **fundamental bond** of `a ∈ T` (`T̄ + a` contains a unique bond,
B&M's out-of-chapter Thm 2.6). Body deferred.

**Book definition** (B&M §12.1, p. 225, verbatim).  *Analogously, if `a` is an arc of
`T`, then `T̄ + a` contains a unique bond (see theorem 2.6).  Let `B_a` denote this
bond and `g_a` the potential difference corresponding to `B_a`, defined so that
`g_a(a) = 1`.*

**Reading.**  Deleting `a` splits its tree in two, and `S` is the vertex set of one
half; the arcs crossing between the halves form the fundamental bond.  The `ν - ω`
fundamental bonds, one per tree arc, give the tree-basis of the bond space, with
`B | T` an identity matrix.  The exact mirror of the fundamental cycle — theorem 2.6
is to bonds and cotrees as theorem 2.5 is to cycles and spanning trees.

**⚠ Defective: `sorry` body.**  Makes `isBasisMatrix_bondSpace_of_maximalForest`
vacuous.

*The repair:* `S` is the set of vertices reachable from `tail a` in `T \ {a}` (using
the underlying-graph reachability of `IsConnectedDigraph`'s repair).  Then
`edgeCutSet tail head S` is the fundamental bond, and `bondPotentialDiff tail head S`
its potential difference — which is why the definition returns the *vertex set*
rather than the bond, letting `bondPotentialDiff` be applied directly.
⚠ Leans on B&M's theorem 2.6, which is out of chapter and not in this repo. -/
def fundamentalBondVertexSet (tail head : A → V) (T : Finset A) (a : A) : Set V := sorry

/-- `B` is the tree-`T` basis matrix of the bond space (rows indexed by `T`). Body deferred.

**Book definition** (B&M §12.1, p. 225, verbatim).  *The `(ν-ω) × ε` matrix `B` whose
rows are `g_a`, `a ∈ T`, is a basis matrix of `𝓑`, called the basis matrix of `𝓑`
corresponding to `T`.*

**Reading.**  Its defining feature is that `B | T` is an identity matrix — the
fundamental bond of `a` contains `a` itself with coefficient `1` and no other tree
arc.  That is what pins down `det(B | T) = 1` in the proof of theorem 12.3, and
what makes exercise 12.1.2(b)'s change-of-basis identity readable.

**⚠ Defective: `sorry` body.**  This predicate is a hypothesis of theorems 12.3,
12.4, corollary 12.4 and exercises 12.2.1(b), 12.2.3(a), 12.2.4(a) — all of which
therefore constrain nothing.

*The repair:* `B` is the tree-`T` basis matrix when its rows are the fundamental-bond
potential differences, i.e.

    B = fun a : {a // a ∈ T} => bondPotentialDiff tail head (fundamentalBondVertexSet tail head T a.1)

— exactly the matrix appearing in `isBasisMatrix_bondSpace_of_maximalForest`.  ⚠
Alternatively, characterise it axiomatically as *"a basis matrix of `𝓑` whose
restriction `B | T` is the identity"*, which is weaker to state, enough for theorem
12.3, and does not depend on `fundamentalBondVertexSet` — probably the better
choice, since it is the property every proof actually uses. -/
def IsBasisMatrixOfTree (tail head : A → V) (T : Finset A) {R : Type*} [CommRing R]
    (B : Matrix {a // a ∈ T} A R) : Prop := sorry

/-- `C` is the tree-`T` basis matrix of the cycle space (rows indexed by `T̄`). Body deferred.

**Book definition** (B&M §12.1, p. 224, verbatim).  *The `(ε-ν+ω) × ε` matrix `C`
whose rows are `f_a`, `a ∈ T̄`, is a basis matrix of `𝓒`.  This follows from the fact
that each row is a circulation and that `rank C = ε - ν + ω` (because `C | T̄` is an
identity matrix).  We refer to `C` as the basis matrix of `𝓒` corresponding to `T`.*

**Reading.**  The cycle-side mirror of `IsBasisMatrixOfTree`: `C | T̄` is the
identity, because the fundamental cycle of `a` is the only one using `a`.

**⚠ Defective: `sorry` body.**  Hypothesis of (12.8), corollary 12.4 and exercises
12.2.1(b), 12.2.4(a) — all vacuous as a result.

*The repair:* as for `IsBasisMatrixOfTree`, either concretely (rows are the
fundamental-cycle circulations) or axiomatically (*a basis matrix of `𝓒` with
`C | T̄` the identity*).  The axiomatic form is again preferable and is what the
determinant arguments actually consume. -/
def IsBasisMatrixOfTree' (tail head : A → V) (T : Finset A) {R : Type*} [CommRing R]
    (C : Matrix {a // a ∉ T} A R) : Prop := sorry

open scoped Classical in
/-- `τ(G)`: the number of spanning trees.

**Book definition** (B&M §2.4).  `τ(G)` denotes the number of spanning trees of `G`.

**Reading.**  The object §12.2 exists to compute.  Theorem 2.8 gave a recursion and
theorem 2.9 a closed formula for complete graphs; chapter 12 finally delivers the
general determinant formula — the **matrix-tree theorem**, implicit in Kirchhoff
(1847).

**⚠ Defective by inheritance.**  `IsSpanningTree` has a `sorry` body, so `tau` counts
an opaque predicate and is itself opaque.  **This is the single most consequential
defect in the file** — every §12.2 result is a statement about `tau`.  Nothing here
needs changing; repairing `IsSpanningTree` repairs this. -/
noncomputable def tau (tail head : A → V) : ℕ :=
  ((Finset.univ : Finset (Finset A)).filter (IsSpanningTree tail head)).card

/-! ## Theorem 12.1: 𝓑 is the row space of M; 𝓒 is its orthogonal complement -/

-- Thm 12.1 (part 1): 𝓑 is the row space of M.
/-- **Theorem 12.1**, first half.  *Let `M` be the incidence matrix of a digraph
`D`.  Then `𝓑` is the row space of `M`.*

**Book proof** (B&M §12.1, verbatim).  *Let `g = δp` be a potential difference in
`D`.  It follows from (12.2) that*

    g(a) = ∑_{v ∈ V} p(v) m_v(a)   for all a ∈ A

*Thus `g` is a linear combination of the rows of `M`.  Conversely, any linear
combination of the rows of `M` is a potential difference.  Hence `𝓑` is the row
space of `M`.*

**Skeleton** (for `bondSpace = span (range M)`).
1. **`⊆`.**  An element of `bondSpace` is `Mᵀ *ᵥ p` for some `p`.  Expand:
   `(Mᵀ *ᵥ p) a = ∑ v, M v a * p v`, which exhibits it as the combination of the rows
   `M v` with coefficients `p v` — so it lies in the span.
2. **`⊇`.**  A member of the span is a finite combination `∑ v, c v • M v`; take
   `p := c` and run step 1 backwards.
3. Both directions are the *same* computation, so prove
   `Mᵀ.mulVecLin p = ∑ v, p v • M v` once and use it twice.

**Reading.**  The drop across `a` is the signed combination of the vertex potentials,
with `m_v` picking out the sign.  So the bond space is *exactly* the row space of
`M`, and `dim 𝓑 = rank M`.

**Formalisation.**  `Submodule.span F (Set.range M)` is the row space, `M` being read
as a family of rows indexed by `V`.  Step 3's identity is the only real content and
is worth extracting, since theorem 12.1's second half needs it too. -/
theorem bondSpace_eq_rowSpace :
    bondSpace tail head (F := F) =
      Submodule.span F (Set.range (orientedIncMatrix tail head F)) := by
  sorry

-- Thm 12.1 (part 2): 𝓒 is the orthogonal complement of 𝓑.
/-- **Theorem 12.1**, second half.  *…and `𝓒` is its orthogonal complement.*

**Book proof** (B&M §12.1, verbatim).  *Now let `f` be a function on `A`.  The
condition (12.1) for `f` to be a circulation can be rewritten as*

    ∑_{a ∈ A} m_v(a) f(a) = 0   for all v ∈ V

*This implies that `f` is a circulation if and only if it is orthogonal to each row
of `M`.  Hence `𝓒` is the orthogonal complement of `𝓑`.*

**Skeleton** (for `cycleSpace = (dotForm F A).orthogonal (bondSpace)`).
1. **Unfold both sides.**  `f ∈ cycleSpace` is `M *ᵥ f = 0`, i.e.
   `∀ v, ∑ a, M v a * f a = 0` — which is `∀ v, dotForm (M v) f = 0`.
2. **Orthogonal to the rows ⟹ orthogonal to their span.**  `dotForm` is bilinear, so
   the set of vectors orthogonal to `f` is a submodule; containing the rows, it
   contains their span, which by theorem 12.1's first half is `𝓑`.
3. **Conversely**, orthogonality to all of `𝓑` gives it for each row, since rows lie
   in `𝓑`.
4. Conclude by `Submodule.ext`.

**Reading.**  This duality is the organising idea of the chapter.  It gives corollary
12.2's dimension formula at once, it makes `BC' = 0` in corollary 12.4, and it is the
source of the cycle/bond symmetry that, as B&M remark, *finds its proper setting in
the theory of matroids*.

**Formalisation.**  ⚠ Note this is orthogonality for a possibly **degenerate** form —
over `ZMod p` a space need not be complementary to its orthogonal, which is exactly
what exercise 12.2.4(b) exploits.  So "orthogonal complement" here means
`BilinForm.orthogonal`, not "complementary subspace"; do not silently use
`dim 𝓑 + dim 𝓒 = ε` in characteristic `p`. -/
theorem cycleSpace_eq_orthogonal_bondSpace :
    cycleSpace tail head (F := F) = (dotForm F A).orthogonal (bondSpace tail head) := by
  sorry

/-! ## Lemma 12.2.1: a nonzero circulation's support contains a cycle -/

-- Lem 12.2.1: a nonzero circulation `f` has an arc-cycle inside its support.
/-- **Lemma 12.2.1.**  *If `f` is a nonzero circulation, then `‖f‖` contains a
cycle.*

**Book proof** (B&M §12.1, verbatim).  *This follows immediately, since `‖f‖` clearly
cannot contain a vertex of degree one.*

**Skeleton** (for `∃ c : ArcCycle, ∀ a ∈ c.arcs, a ∈ support f`).  Unpacking B&M's
one line:
1. **No vertex of `‖f‖` has degree one there.**  If `v` were incident with exactly
   one arc `a` of the support, conservation at `v` (`M *ᵥ f = 0` at row `v`) would
   read `± f a = 0`, contradicting `a ∈ ‖f‖`.  ⚠ Care with loops: a loop at `v`
   contributes `0` to row `v`, so it must be excluded from the degree count.
2. **Minimum degree `≥ 2` forces a cycle** — exercise 1.7.2, applied to the subgraph
   induced by `‖f‖`.
3. `hne` supplies that `‖f‖` is nonempty, so step 1 has something to apply to.

**Reading.**  Current cannot enter a dead end: anything that flows must flow round in
a loop.

**⚠ Currently trivial for the wrong reason.**  Since `ArcCycle` has no closure
condition, the goal is satisfied by the one-element list `[a]` for any `a ∈ ‖f‖` —
so this is provable in two lines and means nothing.  Repair `ArcCycle` before
filling; the skeleton above is for the repaired statement. -/
theorem exists_arcCycle_subset_support_of_isCirculation {f : A → F}
    (hf : f ∈ cycleSpace tail head) (hne : f ≠ 0) :
    ∃ c : ArcCycle tail head, ∀ a ∈ c.arcs, a ∈ Function.support f := by
  sorry

/-! ## Lemma 12.2.2: a nonzero potential difference's support contains a bond -/

-- Lem 12.2.2: a nonzero potential difference `g` has a bond inside its support.
/-- **Lemma 12.2.2.**  *If `g` is a nonzero potential difference, then `‖g‖`
contains a bond.*

**Book proof** (B&M §12.1, verbatim).  *Let `g = δp` be a nonzero potential difference
in `D`.  Choose a vertex `u ∈ V` which is incident with an arc of `‖g‖` and set*

    U = {v ∈ V | p(v) = p(u)}

*Clearly, `‖g‖ ⊇ [U, Ū]` since `g(a) ≠ 0` for all `a ∈ [U, Ū]`.  But, by the choice
of `u`, `[U, Ū]` is nonempty.  Thus `‖g‖` contains a bond.*

**Skeleton** (for `∃ B, IsBond B ∧ B ⊆ support g`).
1. `hg` gives `p` with `g = δp`; `hne` gives an arc `a₀` with `g a₀ ≠ 0`, hence
   `p (tail a₀) ≠ p (head a₀)`.  Take `u := tail a₀`.
2. Set `U := {v | p v = p u}`.  Every `a ∈ edgeCutSet U` has its ends at different
   potentials, so `g a ≠ 0` — giving `edgeCutSet U ⊆ support g`.
3. `edgeCutSet U` is nonempty: `a₀` is in it, since `p (head a₀) ≠ p u`.
4. **From edge cut to bond** — ⚠ the step B&M compress into "thus `‖g‖` contains a
   bond".  A nonempty edge cut contains a *minimal* nonempty edge cut, by finiteness:
   descend through sub-edge-cuts until none is a proper one.  This needs `IsBond`'s
   minimality clause and is the only real work.

**Reading.**  The exact dual of lemma 12.2.1; the two together drive theorem 12.2.

**Formalisation.**  Step 4 is where `IsBond`'s minimality is consumed — see that
definition's note about what "minimal among edge cuts" quantifies over. -/
theorem exists_isBond_subset_support_of_mem_bondSpace {g : A → F}
    (hg : g ∈ bondSpace tail head) (hne : g ≠ 0) :
    ∃ B, IsBond tail head B ∧ B ⊆ Function.support g := by
  sorry

/-! ## Theorem 12.2: linear independence of columns ⟺ acyclic / bond-free -/

-- Thm 12.2(i): columns of B|S independent ⟺ S acyclic.
/-- **Theorem 12.2(i).**  *Let `B` be a basis matrix of `𝓑`.  Then for any `S ⊆ A`,
the columns of `B | S` are linearly independent if and only if `S` is acyclic.*

**Book proof** (B&M §12.1, verbatim).  *Denote the column of `B` corresponding to arc
`a` by `B(a)`.  The columns of `B | S` are linearly dependent if and only if there
exists a function `f` on `A` such that*

    f(a) ≠ 0  for some a ∈ S
    f(a) = 0  for all a ∉ S
    ∑_{a ∈ A} f(a) B(a) = O

*We conclude that the columns of `B | S` are linearly dependent if and only if there
exists a nonzero circulation `f` such that `‖f‖ ⊆ S`.  Now if there is such an `f`
then, by lemma 12.2.1, `S` contains a cycle.  On the other hand, if `S` contains a
cycle `C`, then `f_C` is a nonzero circulation with `‖f_C‖ = C ⊆ S`.  It follows
that the columns of `B | S` are linearly independent if and only if `S` is
acyclic.*

**Skeleton** (for `LinearIndependent (columns of B|S) ↔ IsArcAcyclic S`).  Prove the
contrapositive throughout — *dependent ↔ contains a cycle*.
1. **Dependence ⟹ a vector in `𝓑`'s orthogonal complement.**  A dependency is an
   `f` supported in `S`, not identically zero, with `∑_a f a • B(a) = 0` — i.e. `f`
   is orthogonal to every row of `B`, hence (rows spanning `𝓑`) to all of `𝓑`.
2. **Theorem 12.1** identifies that complement as `𝓒`, so `f` is a nonzero
   circulation with `‖f‖ ⊆ S`.
3. **Lemma 12.2.1** turns it into a cycle inside `S`.
4. **Converse.**  A cycle `C ⊆ S` gives `f_C`, a nonzero circulation with
   `‖f_C‖ = C ⊆ S`; reading step 1 backwards gives the dependency.

**Reading.**  The theorem converting a combinatorial question into a linear-algebraic
one — and it holds over **any** field, which is why exercise 12.1.5 is subsumed by
stating §12.1 over `[Field F]`.

**⚠ Currently false.**  With `ArcCycle` degenerate, `IsArcAcyclic S ↔ S = ∅`, so the
right-hand side says `S = ∅` while the left is true for any independent column set.
Repair `ArcCycle` first.  Step 4 additionally needs `cycleCirculation`, also
`sorry`-bodied. -/
theorem basisMatrix_bondSpace_cols_linearIndependent_iff
    (S : Finset A) {B : Matrix n A F} (hB : IsBasisMatrix B (bondSpace tail head)) :
    LinearIndependent F (fun a : {a // a ∈ S} => (restrictCols B S)ᵀ a) ↔
      IsArcAcyclic tail head S := by
  sorry

-- Thm 12.2(ii): columns of C|S independent ⟺ S contains no bond.
-- ⚠ B&M prove this with "A similar argument" — it is a second theorem, not a symmetry.
/-- **Theorem 12.2(ii).**  *Let `C` be a basis matrix of `𝓒`.  Then for any
`S ⊆ A`, the columns of `C | S` are linearly independent if and only if `S`
contains no bond.*

**Book proof** (B&M §12.1, verbatim).  *A similar argument using lemma 12.2.2 yields a
proof of (ii).*

**Skeleton** (for `LinearIndependent (columns of C|S) ↔ ¬ ∃ bond ⊆ S`).  Mirror of
(i), with the spaces exchanged.
1. Dependence gives a nonzero `f` supported in `S`, orthogonal to every row of `C`
   and hence to all of `𝓒`.
2. **⚠ The step that is *not* a mirror.**  Part (i) used theorem 12.1's
   `𝓒 = 𝓑^⊥`; here one needs `𝓑 = 𝓒^⊥`, the *reverse* inclusion, which theorem 12.1
   does not directly state.  Over a field where the form is nondegenerate this is
   double-orthogonality (`W^⊥⊥ = W` for finite-dimensional `W`); over `ZMod p` it
   needs care.  Establish `𝓒^⊥ = 𝓑` explicitly before proceeding.
3. **Lemma 12.2.2** turns the resulting potential difference into a bond inside `S`.
4. **Converse.**  A bond `B ⊆ S` gives `g_B = bondPotentialDiff S`, supported on `B`.

**Reading.**  B&M dispatch this with *"a similar argument"*, but it is genuinely a
second theorem rather than a formal symmetry: `𝓒` is defined as a **kernel** and `𝓑`
as a **range**, so step 2 has no counterpart in part (i).

**Formalisation.**  Step 2 is the whole reason this deserves separate treatment;
budget for it rather than expecting the (i) proof to transport. -/
theorem basisMatrix_cycleSpace_cols_linearIndependent_iff
    (S : Finset A) {C : Matrix n A F} (hC : IsBasisMatrix C (cycleSpace tail head)) :
    LinearIndependent F (fun a : {a // a ∈ S} => (restrictCols C S)ᵀ a) ↔
      ¬ ∃ B, IsBond tail head B ∧ B ⊆ (S : Set A) := by
  sorry

/-! ## Corollary 12.2: dim 𝓑 = ν − ω and dim 𝓒 = ε − ν + ω -/

-- Cor 12.2 (12.3): dim 𝓑 = ν − ω.
/-- **Corollary 12.2**, formula (12.3).  *`dim 𝓑 = ν - ω`.*

**Book proof** (B&M §12.1, verbatim).  *Consider a basis matrix `B` of `𝓑`.  By
theorem 12.2*

    rank B = max{|S| : S ⊆ A, S acyclic}

*The above maximum is attained when `S` is a maximal forest of `D`, and is therefore
(exercise 2.2.4) equal to `ν - ω`.  Since `dim 𝓑 = rank B`, this establishes
(12.3).*

**Skeleton** (for `finrank 𝓑 = card V - card G.ConnectedComponent`).
1. Take any basis matrix `B` of `𝓑` — e.g. `M` itself is a spanning set, so a basis
   can be extracted; `dim 𝓑 = rank B`.
2. **Column rank via theorem 12.2(i).**  `rank B` equals the largest size of an
   independent column set, which by 12.2(i) is the largest acyclic `S`.
3. **The largest acyclic set is a maximal forest, of size `ν - ω`** — B&M's exercise
   2.2.4, which this repo does not have and which must be proved: a maximal forest
   has one fewer arc than vertices in each component.
4. Rewrite `ω` as `card G.ConnectedComponent` via `hG`.

**Reading.**  The bond space records the vertex potentials — `ν` of them — modulo an
additive constant on each of the `ω` components, leaving `ν - ω` degrees of freedom.

**Formalisation.**  ⚠ Stated over `ℝ` specifically, unlike the rest of §12.1 which is
over a general `[Field F]`; the dimension count is in fact field-independent, so this
could be generalised.  Step 3 is the out-of-chapter import to budget for.  Note the
ℕ-subtraction `card V - card ConnectedComponent` never truncates, since `ω ≤ ν`. -/
theorem finrank_bondSpace (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsUnderlyingGraph tail head G) :
    Module.finrank ℝ (bondSpace tail head (F := ℝ)) =
      Fintype.card V - Fintype.card G.ConnectedComponent := by
  sorry

-- Cor 12.2 (12.4): dim 𝓒 = ε − ν + ω.  ⭐ one `finrank_orthogonal` call.
/-- **Corollary 12.2**, formula (12.4).  *`dim 𝓒 = ε - ν + ω`.*

**Book proof** (B&M §12.1, verbatim).  *Now (12.4) follows, since `𝓒` is the
orthogonal complement of `𝓑`.*

**Skeleton** (for `finrank 𝓒 = card A - card V + card G.ConnectedComponent`).
1. `cycleSpace` is `ker M.mulVecLin`, so **rank–nullity** gives
   `finrank 𝓒 = card A - rank M` directly — no orthogonality needed.
2. `rank M = finrank 𝓑` by theorem 12.1's first half (`𝓑` is the row space).
3. Corollary 12.2's first half gives `finrank 𝓑 = ν - ω`; substitute.
4. ⚠ Arrange the ℕ-arithmetic as `card A - card V + ω` without intermediate
   truncation — `ν - ω ≤ card A` holds but is worth establishing before subtracting.

**Reading.**  `ε - ν + ω` is the **cycle rank** or first Betti number — the number of
independent cycles, and exactly the number of arcs outside a maximal forest.  That
count is realised concretely by the fundamental cycles, one per non-tree arc.

**Formalisation.**  ⚠ B&M derive this from orthogonality (`dim 𝓒 = ε - dim 𝓑`),
which is valid over `ℝ` but **not** in characteristic `p`, where the form is
degenerate and the two spaces can overlap (exercise 12.2.4(b)).  The rank–nullity
route of step 1 is field-independent and therefore both simpler and more robust —
prefer it. -/
theorem finrank_cycleSpace (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsUnderlyingGraph tail head G) :
    Module.finrank ℝ (cycleSpace tail head (F := ℝ)) =
      Fintype.card A - Fintype.card V + Fintype.card G.ConnectedComponent := by
  sorry

/-! ## T-basis matrices (p. 224–225) — extracted from B&M's prose -/

-- T-basis of 𝓒: rows `f_a`, `a ∈ T̄`, form a basis matrix of the cycle space.
/-- **Book construction (§12.1, p. 224).**  *The `(ε-ν+ω) × ε` matrix `C` whose rows
are `f_a`, `a ∈ T̄`, is a basis matrix of `𝓒`.*

**Book proof** (B&M §12.1, verbatim).  *This follows from the fact that each row is a
circulation and that `rank C = ε - ν + ω` (because `C | T̄` is an identity matrix).*

**Skeleton** (for `IsBasisMatrix (fun a : T̄ => f_a) 𝓒`).
1. **Each row lies in `𝓒`.**  `f_a` is the circulation of a cycle, and a cycle
   circulation satisfies conservation at every vertex — the cycle enters and leaves
   each of its vertices exactly once.  Prove this once as a lemma about
   `cycleCirculation`; it is used again in theorem 12.2(i)'s converse.
2. **`C | T̄` is the identity.**  `f_a(a) = 1` by the normalisation, and `f_a(b) = 0`
   for `b ∈ T̄`, `b ≠ a`, because the fundamental cycle of `a` uses only `a` and tree
   arcs.
3. **Independence** follows: a matrix with an identity submatrix has full row rank.
4. **Spanning.**  There are `ε - ν + ω` rows, which by corollary 12.2 equals
   `dim 𝓒`; independent and of the right count, so a basis.

**Reading.**  The **fundamental cycle basis** — the concrete realisation of the claim
that every circulation is a combination of cycle circulations, which is what gave the
cycle space its name.

**⚠ Currently vacuous.**  Three of the four ingredients — `IsMaximalForest`,
`fundamentalCycle`, `cycleCirculation` — have `sorry` bodies. -/
theorem isBasisMatrix_cycleSpace_of_maximalForest
    (T : Finset A) (hT : IsMaximalForest tail head T) :
    IsBasisMatrix
      (fun a : {a // a ∉ T} => cycleCirculation tail head (fundamentalCycle tail head T hT a.2))
      (cycleSpace tail head (F := F)) := by
  sorry

-- T-basis of 𝓑: rows `g_a`, `a ∈ T`, form a basis matrix of the bond space.
-- ⚠ needs B&M's out-of-chapter Theorem 2.6.
/-- **Book construction (§12.1, p. 225).**  *The `(ν-ω) × ε` matrix `B` whose rows
are `g_a`, `a ∈ T`, is a basis matrix of `𝓑`, called the basis matrix of `𝓑`
corresponding to `T`.*

**Book proof.**  None stated — B&M assert the analogue of the cycle case, citing
theorem 2.6 for the uniqueness of the bond in `T̄ + a`.

**Skeleton** (for `IsBasisMatrix (fun a : T => g_a) 𝓑`).  Mirror of the cycle case.
1. **Each row lies in `𝓑`.**  `g_a = bondPotentialDiff S` is by construction `δp`
   for `p` the indicator of `S`, so membership is immediate — easier than the cycle
   side, where conservation had to be checked.
2. **`B | T` is the identity.**  `g_a(a) = 1` by normalisation, and `g_a(b) = 0` for
   other tree arcs `b`, since the fundamental bond of `a` meets `T` only in `a` —
   this is the content of theorem 2.6.
3. **Independence** from the identity submatrix, as before.
4. **Spanning** by the count `ν - ω = dim 𝓑` (corollary 12.2).

**Reading.**  The **fundamental bond basis**, realising the claim that every
potential difference is a combination of bond potential differences.

**⚠ Currently vacuous** — `IsMaximalForest` and `fundamentalBondVertexSet` both have
`sorry` bodies.  ⚠ Step 2 also leans on B&M's theorem 2.6, which is out of chapter
and absent from this repo. -/
theorem isBasisMatrix_bondSpace_of_maximalForest
    (T : Finset A) (hT : IsMaximalForest tail head T) :
    IsBasisMatrix
      (fun a : {a // a ∈ T} =>
        bondPotentialDiff tail head (fundamentalBondVertexSet tail head T a.1))
      (bondSpace tail head (F := F)) := by
  sorry

/-! ## Theorem 12.3: the basis matrix B is unimodular -/

-- Thm 12.3: the tree-basis matrix B of 𝓑 is unimodular (full submatrices only).
/-- **Theorem 12.3** (proof due to Tutte, 1965b).  *The basis matrix `B` is
unimodular.*

**Book proof** (B&M §12.2, verbatim).  *Let `P` be a full submatrix of `B` (one of
order `ν - 1`).  Suppose that `P = B | T₁`.  We may assume that `T₁` is a spanning
tree of `D` since, otherwise, `det P = 0` by theorem 12.2.  Let `B₁` denote the basis
matrix of `𝓑` corresponding to `T₁`.  Then (exercise 12.1.2b)*

    (B | T₁) B₁ = B

*Restricting both sides to `T`, we obtain `(B | T₁)(B₁ | T) = B | T`.  Noting that
`B | T` is an identity matrix, and taking determinants, we get*

    det(B | T₁) det(B₁ | T) = 1                                      (12.5)

*Both determinants in (12.5), being determinants of integer matrices, are themselves
integers.  It follows that `det(B | T₁) = ±1`.*

**Skeleton** (for `B.IsUnimodular`).
1. `intro g hg`; the injective `g : T → A` picks out `T₁ := range g`, a set of
   `ν - 1` arcs, and the goal is `det (B | T₁) ∈ {0, 1, -1}`.
2. **Case `T₁` not a spanning tree.**  Theorem 12.2(i) makes the columns dependent,
   so the square matrix is singular and `det = 0`.
3. **Case `T₁` a spanning tree.**  Let `B₁` be its tree-basis matrix.  Exercise
   12.1.2(b) gives `(B | T₁) B₁ = B`; restrict to `T`'s columns.
4. `B | T = 1` (the defining property of a tree-basis matrix), so taking
   determinants, `det(B | T₁) · det(B₁ | T) = 1` in `ℤ`.
5. `Int.eq_one_or_self_of_prime`-style: two integers with product `1` are both `±1`
   (`Int.isUnit_iff`).

**Reading.**  Exactly what theorem 12.4 needs: every full submatrix contributes `0`
or a determinant of absolute value `1`, so squaring and summing counts the spanning
trees.  The proof is due to Tutte (1965b).

**⚠ Currently vacuous** — `IsSpanningTree` and `IsBasisMatrixOfTree` both have
`sorry` bodies.  Note step 4 is where the *axiomatic* reading of
`IsBasisMatrixOfTree` (*"basis matrix with `B | T` the identity"*) would pay off
directly. -/
theorem isUnimodular_basisMatrix_bondSpace
    (T : Finset A) (hT : IsSpanningTree tail head T)
    {B : Matrix {a // a ∈ T} A ℤ} (hB : IsBasisMatrixOfTree tail head T B) :
    B.IsUnimodular := by
  sorry

/-! ## Theorem 12.4: τ(G) = det BB′  (12.6) -/

-- TODO(Matrix.det_mul_transpose_eq_sum_sq_det_submatrix): Cauchy–Binet, B&M's (12.7).
-- ⚠ ABSENT from Mathlib, and its faithful statement cannot elaborate here: the square
-- submatrix on a subset `S` of columns is indexed by `{a // a ∈ S}` (size `card ι`), not by
-- `ι`, so `Matrix.det` is ill-typed without a per-subset `{a // a ∈ S} ≃ ι` equiv threaded
-- through the sum. Left unstated; B&M outsource it by citation ("see Hadley, 1961").

/-! ### Book statement of the deferred item

*Formula (12.7), the Cauchy–Binet formula.*  For a rectangular matrix `B` with
`ν - 1` rows and `ε` columns,

    det BB' = ∑_{S ⊆ A, |S| = ν-1} (det(B | S))².

**Reading.**  The determinant of `BB'` expands as a sum over all ways of choosing as
many columns as there are rows, each contributing the square of the corresponding
minor.  B&M outsource it by citation (*"see Hadley, 1961"*).

**Formalisation.**  ⚠ Absent from Mathlib, and its faithful statement will not
elaborate cleanly here: the square submatrix on a subset `S` of columns is indexed by
`{a // a ∈ S}`, of size `card ι` but not *equal* to `ι`, so `Matrix.det` is ill-typed
without threading a per-subset equiv `{a // a ∈ S} ≃ ι` through the sum.  Left
unstated rather than mis-stated.

*Routes if it is needed:* either (i) index the sum by injections `ι ↪ A` and divide
by the `card ι !` orderings, or (ii) fix, for each `S`, an equivalence via
`Finset.orderIsoOfFin` and prove the result independent of the choice.  (ii) is
closer to the book but needs `A` linearly ordered; (i) avoids that.  Both are real
work — this is the single largest missing import for §12.2. -/

-- Thm 12.4: τ(G) = det BB′ for a tree-basis matrix B of 𝓑.
/-- **Theorem 12.4.**  *`τ(G) = det BB'`* (12.6).

**Book proof** (B&M §12.2, verbatim).  *Using the formula for the determinant of the
product of two rectangular matrices (see Hadley, 1961), we obtain*

    det BB' = ∑_{S ⊆ A, |S| = ν-1} (det(B | S))²                     (12.7)

*Now, by theorem 12.2, the number of nonzero terms in (12.7) is equal to `τ(G)`.
But, by theorem 12.3, each such term has value 1.*

**Skeleton** (for `(τ : ℤ) = det (B * Bᵀ)`).
1. **Cauchy–Binet (12.7)** — ⚠ absent from Mathlib and left unstated here (see the
   TODO block above); it must be supplied first, and its statement is the awkward
   part, the square submatrix being indexed by a subtype rather than a fixed type.
2. **Classify the terms.**  Theorem 12.2(i): `det(B | S) ≠ 0` iff the columns are
   independent iff `S` is acyclic; with `|S| = ν - 1` that is exactly "`S` is a
   spanning tree".
3. **Evaluate the nonzero terms.**  Theorem 12.3 makes each such determinant `±1`,
   so each squared term is `1`.
4. **Count.**  The sum is therefore the number of spanning trees, `τ(G)`.

**Reading.**  The chapter's central computation: the number of spanning trees, a
purely combinatorial quantity, is a determinant.  Compare theorem 2.8's
deletion–contraction recursion, which B&M called impractical for large graphs, and
theorem 2.9's Cayley formula, valid only for complete graphs — this is general and
efficiently computable.

**⚠ Currently vacuous** — `tau` (via `IsSpanningTree`) and `IsBasisMatrixOfTree` both
rest on `sorry` bodies.  Step 1 is an additional, substantial import. -/
theorem tau_eq_det_mul_transpose
    (T : Finset A) (hT : IsSpanningTree tail head T)
    {B : Matrix {a // a ∈ T} A ℤ} (hB : IsBasisMatrixOfTree tail head T B) :
    (tau tail head : ℤ) = (B * Bᵀ).det := by
  sorry

/-! ## (12.8): τ(G) = det CC′ — extracted from B&M's prose ("One can similarly show…") -/

-- (12.8) part 1: the tree-basis matrix C of 𝓒 is unimodular (dual of Thm 12.3).
/-- **Book remark following theorem 12.4.**  *One can similarly show that if `C` is
a basis matrix of `𝓒` corresponding to a tree, then `C` is unimodular…*

**Book proof.**  None — B&M write only *One can similarly show…*, leaving the cycle
side to the reader.

**Skeleton** (for `C.IsUnimodular`).  Mirror of theorem 12.3.
1. A full submatrix of `C` has order `ε - ν + ω` and selects a set `T̄₁` of that many
   columns.
2. **If `T̄₁` is not the complement of a spanning tree**, theorem 12.2(**ii**) — not
   (i) — makes the columns dependent and the determinant `0`.
3. **Otherwise** the change-of-basis identity `(C | T̄₁) C₁ = C`, restricted to `T̄`
   where `C | T̄` is the identity, forces `det(C | T̄₁) · det(C₁ | T̄) = 1` and hence
   `±1`.

**Reading.**  The chapter is organised around such dual pairs — cycles and bonds,
kernels and ranges, trees and cotrees.

**Formalisation.**  ⚠ Step 3 needs the cycle-side analogue of exercise 12.1.2(b),
which is stated in this file only for `𝓑` (`basisMatrix_eq_restrict_mul`).  The
cycle version must be proved separately, and — as noted under theorem 12.2(ii) — the
`𝓒`-side arguments are not formal transports of the `𝓑`-side ones. -/
theorem isUnimodular_basisMatrix_cycleSpace
    (T : Finset A) (hT : IsSpanningTree tail head T)
    {C : Matrix {a // a ∉ T} A ℤ} (hC : IsBasisMatrixOfTree' tail head T C) :
    C.IsUnimodular := by
  sorry

-- (12.8) part 2: τ(G) = det CC′ (dual of Thm 12.4).
/-- **Book formula (12.8).**  *…and `τ(G) = det CC'`.*

**Book proof.**  None — asserted alongside the unimodularity claim as *"…and
`τ(G) = det CC'`"*.

**Skeleton** (for `(τ : ℤ) = det (C * Cᵀ)`).  Exactly theorem 12.4 with `𝓒` for `𝓑`:
Cauchy–Binet expands `det CC'` as a sum of squared minors; theorem 12.2(ii) makes the
nonzero terms correspond to *complements* of spanning trees; the previous result
makes each contribute `1`; and complements biject with spanning trees, so the count
is again `τ(G)`.

**Reading.**  The spanning trees can be counted from either space — through the bonds
or through the cycles.  Corollary 12.4 combines the two computations into one
determinant.

**⚠ Currently vacuous** — `tau` and `IsBasisMatrixOfTree'` both rest on `sorry`
bodies; and Cauchy–Binet is still missing. -/
theorem tau_eq_det_mul_transpose_cycleSpace
    (T : Finset A) (hT : IsSpanningTree tail head T)
    {C : Matrix {a // a ∉ T} A ℤ} (hC : IsBasisMatrixOfTree' tail head T C) :
    (tau tail head : ℤ) = (C * Cᵀ).det := by
  sorry

/-! ## Corollary 12.4: τ(G) = ±det [B; C] -/

-- Cor 12.4: τ(G) = ± det of the stacked matrix [B; C] (row-reindexed to A via `Equiv.sumCompl`).
/-- **Corollary 12.4.**  *`τ(G) = ± det [B; C]`*, the determinant of the square
matrix obtained by stacking a tree-basis matrix of `𝓑` on top of one of `𝓒`.

**Book proof** (B&M §12.2, verbatim).  *By (12.6) and (12.8)*

    (τ(G))² = det BB' · det CC' = det [[BB', 0], [0, CC']]

*Since `𝓑` and `𝓒` are orthogonal, `BC' = CB' = 0`.  Thus*

    (τ(G))² = det [[BB', BC'], [CB', CC']] = det ([B; C] [B' | C'])
            = det [B; C] · det [B' | C'] = (det [B; C])²

*The corollary follows on taking square roots.*

**Skeleton** (for `(τ : ℤ) = det [B;C] ∨ (τ : ℤ) = -det [B;C]`).
1. Theorem 12.4 and (12.8) give `τ² = det BB' · det CC'`.
2. **`BC' = 0` and `CB' = 0`** from theorem 12.1's orthogonality: every row of `B` is
   in `𝓑`, every row of `C` in `𝓒`, and `𝓒 = 𝓑^⊥`.
3. Assemble the block matrix and use `Matrix.det_fromBlocks_zero₁₂` (or `…₂₁`) for
   the block-diagonal determinant, then `Matrix.det_mul` on `[B;C] · [B'|C']`.
4. `det [B'|C'] = det [B;C]` (transpose), so `τ² = (det [B;C])²`; conclude
   `τ = ±det` by `sq_eq_sq'` / `Int.eq_or_eq_neg_of_sq_eq_sq`.

**Reading.**  The stacked matrix is square because
`dim 𝓑 + dim 𝓒 = (ν - ω) + (ε - ν + ω) = ε` — the two spaces are complementary,
which is theorem 12.1's orthogonality counted dimensionally.

**Formalisation.**  The `∨` in the conclusion is the book's `±`.  The row index is
`{a // a ∈ T} ⊕ {a // a ∉ T}`, reindexed to `A` by `Equiv.sumCompl` — that equiv is
canonical here, unlike in exercise 12.2.1(b) where one must be supplied.
⚠ Currently vacuous, resting on `tau` and both `IsBasisMatrixOfTree` predicates. -/
theorem tau_eq_det_fromBlocks
    (T : Finset A) (hT : IsSpanningTree tail head T)
    {B : Matrix {a // a ∈ T} A ℤ} {C : Matrix {a // a ∉ T} A ℤ}
    (hB : IsBasisMatrixOfTree tail head T B) (hC : IsBasisMatrixOfTree' tail head T C) :
    (tau tail head : ℤ) =
        ((Matrix.of (Sum.elim B C)).submatrix (Equiv.sumCompl (· ∈ T)).symm id).det ∨
      (tau tail head : ℤ) =
        -((Matrix.of (Sum.elim B C)).submatrix (Equiv.sumCompl (· ∈ T)).symm id).det := by
  sorry

/-! ## Matrix-tree theorem: τ(G) = det KK′ (Kirchhoff, 1847) — extracted from B&M's prose -/

-- Matrix-tree theorem: for connected D, τ(G) = det(K Kᵀ) where K deletes one row of M.
/-- **The matrix-tree theorem** (implicit in Kirchhoff, 1847).  *`τ(G) = det KK'`,
where `K` is obtained from the incidence matrix `M` by deleting any one row.*

**Book proof** (B&M §12.2, verbatim).  *Since theorem 12.2 is valid for all basis
matrices of `𝓑`, (12.6) clearly holds for any such matrix `B` that is unimodular.
In particular, a matrix `K` obtained by deleting any one row of the incidence matrix
`M` is unimodular (exercise 12.2.1a).  Thus `τ(G) = det KK'`.  This expression for
the number of spanning trees in a graph is implicit in the work of Kirchhoff (1847),
and is known as the matrix-tree theorem.*

**Skeleton** (for `(τ : ℤ) = det (K * Kᵀ)`, `K` = `M` with row `y` deleted).
1. **`K` is a basis matrix of `𝓑`** — exercise 12.1.3, which is where `hconn` is
   spent.
2. **`K` is unimodular** — exercise 12.2.1(a).
3. **Generalise theorem 12.4.**  ⚠ Its statement here is tied to
   `IsBasisMatrixOfTree`, i.e. to *tree* basis matrices, whereas B&M's argument needs
   it for **any** unimodular basis matrix.  So either restate theorem 12.4 with the
   weaker hypothesis (*`B` a unimodular basis matrix of `𝓑`*) — which is what its
   proof actually uses — or prove this case separately.  Restating is better: the
   tree hypothesis is used nowhere in theorem 12.4's argument except to supply
   unimodularity.
4. Apply the generalised 12.4 to `K`.

**Reading.**  The rows of `M` sum to zero — every arc contributes `+1` at its tail
and `-1` at its head — so exactly one row is redundant, and discarding it leaves an
independent spanning set of `𝓑`.  By exercise 12.2.2(a) the product `MM'` is the
**Laplacian** (B&M's *conductance matrix*), so this says every cofactor of the
Laplacian equals `τ(G)` — the form in which the matrix-tree theorem is usually
quoted, and the closed formula for `τ(G)` promised back in §2.4.

**⚠ Currently vacuous** — `tau` and `IsConnectedDigraph` both rest on `sorry` bodies.
Step 3 is a genuine restructuring worth doing before any of §12.2 is filled. -/
theorem matrix_tree_theorem (hconn : IsConnectedDigraph tail head) (y : V) :
    (tau tail head : ℤ) =
      ((orientedIncMatrix tail head ℤ).submatrix (fun v : {v // v ≠ y} => (v : V)) id *
        ((orientedIncMatrix tail head ℤ).submatrix
          (fun v : {v // v ≠ y} => (v : V)) id)ᵀ).det := by
  sorry

/-! ## Exercises -/

-- Ex 12.2.1(a)*: deleting one row of M gives a unimodular matrix K.
/-- **Exercise 12.2.1(a)***.  *A matrix `K` obtained from `M` by deleting any one row
is unimodular.*

**Book proof.**  None — an exercise, and one the book **stars**.

**Skeleton** (for `K.IsUnimodular`).
1. A full square submatrix selects `ν - 1` arcs `S`.
2. **If `S` contains a cycle**, the columns are dependent (theorem 12.2(i), `K` being
   a basis matrix by exercise 12.1.3) and the determinant is `0`.
3. **If `S` is a spanning tree**, induct on `ν`: a tree on `≥ 2` vertices has a leaf
   `u ≠ y`, whose row in `K | S` has exactly one nonzero entry, `±1`.  Expand the
   determinant along that row; the minor is the corresponding matrix for the tree
   with the leaf removed.  By induction it is `±1`, so the whole determinant is.
4. Base case `ν = 1`: the empty matrix, determinant `1`.

**Reading.**  The incidence-matrix counterpart of theorem 12.3, and what upgrades
exercise 12.1.3 into the matrix-tree theorem `τ(G) = det KK'`.  Note it is proved
*directly*, not via theorem 12.3 — `K` is not a tree-basis matrix.

**Formalisation.**  ⚠ Step 3's leaf induction is the real work and has no counterpart
in theorem 12.3's slick change-of-basis argument.  ⚠ The statement lacks a
connectivity hypothesis, unlike `isBasisMatrix_deleteRow`; step 2 uses that `K` is a
basis matrix, which *does* need `hconn` — so either add it or find a route through
step 3 alone. -/
theorem isUnimodular_deleteRow (y : V) :
    ((orientedIncMatrix tail head ℤ).submatrix
      (fun v : {v // v ≠ y} => (v : V)) id).IsUnimodular := by
  sorry

-- Ex 12.2.2(a): the Laplacian (B&M's conductance matrix) equals M Mᵀ.  ⭐ cheapest win.
/-- **Exercise 12.2.2(a).**  *The conductance matrix `C` of a loopless graph `G`
satisfies `C = MM'`, where `M` is the incidence matrix of any orientation of `G`.*

**Book definition.**  *The conductance matrix `C = [c_ij]` of a loopless graph `G`
is the `ν × ν` matrix with `c_ii = ∑_{j ≠ i} a_ij` and `c_ij = -a_ij` for
`i ≠ j`, where `A` is the adjacency matrix.*

**Book proof.**  None — an exercise.

**Skeleton** (for `G.lapMatrix ℤ = M * Mᵀ`).
1. `Matrix.ext`; fix `u`, `v`.  The `(u,v)` entry of `M * Mᵀ` is `∑ a, m_u a * m_v a`.
2. **Diagonal `u = v`:** each arc incident with `u` contributes `(±1)² = 1`, others
   `0`; the sum is `deg u`.  ⚠ A loop at `u` contributes `0`, since
   `m_u a = 1 - 1 = 0` — consistent with `lapMatrix` being defined for a
   `SimpleGraph`, which has no loops, but worth checking against `hor`.
3. **Off-diagonal `u ≠ v`:** an arc joining them contributes `(+1)(-1) = -1` whichever
   way it points; other arcs contribute `0`.  The sum is `-(number of joining arcs)`,
   which `hor` identifies with `-A u v`.  ⚠ Parallel arcs would make this `-k`, not
   `-1` — `hor` only says the underlying *simple* graph is `G`, so either assume at
   most one arc per pair or state the result for a multigraph Laplacian.
4. Match against `lapMatrix = degMatrix - adjMatrix`.

**Reading.**  ★ **The cheapest win in the file** — a direct computation, no dependency
on the defective definitions.  This is what Mathlib calls the **Laplacian**; B&M call
it the *conductance matrix*.  Notably the *orientation drops out* — the signs cancel
— so it is an invariant of the undirected graph, as it must be.

**Formalisation.**  Step 3's parallel-arc caveat is the one thing to pin down before
starting; everything else is `Finset.sum` manipulation. -/
theorem lapMatrix_eq_orientedIncMatrix_mul_transpose
    (G : SimpleGraph V) [DecidableRel G.Adj] (hor : IsOrientationOf tail head G) :
    G.lapMatrix ℤ = orientedIncMatrix tail head ℤ * (orientedIncMatrix tail head ℤ)ᵀ := by
  sorry

-- Ex 12.2.2(b): the matrix-tree theorem in cofactor form.
-- NOTE: stated as the principal `(y,y)`-minor of the Laplacian equalling τ(G).
/-- **Exercise 12.2.2(b).**  *All cofactors of the conductance matrix `C` are equal
to `τ(G)`.*

**Book proof.**  None — an exercise.

**Skeleton** (for `(τ : ℤ) = det (lapMatrix with row and column y deleted)`).
1. **Part (a)** gives `lapMatrix = M * Mᵀ`.
2. **Deleting row and column `y` commutes with the product**:
   `(M * Mᵀ)` restricted to `{v // v ≠ y}` on both sides equals `K * Kᵀ`, where
   `K` is `M` with row `y` deleted.  This is the only computational step —
   `Matrix.submatrix_mul` with the column index untouched.
3. **The matrix-tree theorem** gives `τ = det (K * Kᵀ)`.
4. Chain.

**Reading.**  The form in which the matrix-tree theorem is normally stated: *the
number of spanning trees is any cofactor of the Laplacian*.  It finally delivers, in
full generality, the closed formula for `τ(G)` that §2.4 promised and that theorem
2.9 gave only for complete graphs.

**Formalisation.**  This states the *principal* `(y,y)`-minor, which is what the
matrix-tree theorem gives directly and what every application uses.  B&M claim
**all** cofactors equal `τ(G)`, including the non-principal ones; that full statement
is `tau_eq_lapMatrix_cofactor` directly below, and this principal case is the one to
prove first. -/
theorem tau_eq_det_lapMatrix_deleteRowCol
    (G : SimpleGraph V) [DecidableRel G.Adj] (hor : IsOrientationOf tail head G) (y : V) :
    (tau tail head : ℤ) =
      ((G.lapMatrix ℤ).submatrix
        (fun v : {v // v ≠ y} => (v : V)) (fun v : {v // v ≠ y} => (v : V))).det := by
  sorry

-- Ex 12.2.2(b), full form: *all* cofactors of the Laplacian equal τ(G), not just the
-- principal ones.  This is the exercise as B&M state it.
/-- **Exercise 12.2.2(b)**, full form.  *All cofactors of the conductance matrix `C`
are equal to `τ(G)`.*

## Book statement (§12.2) — verbatim

> Show that all cofactors of the conductance matrix `C` are equal to `τ(G)`.

An exercise, so the book gives no proof.

## Provenance

**Restored transcription.**  `tau_eq_det_lapMatrix_deleteRowCol` above states only the
principal `(y,y)`-minor.  The triage (`log/graphtheory-EXERCISE_TRIAGE.md` §A.11)
recorded this as a fidelity gap and recommended stating the exercise as written.  The
general form is the one usually cited, because it is what licenses deleting *any* row
and *any* column — the principal case alone does not.

## Skeleton

1. **Principal case.**  `tau_eq_det_lapMatrix_deleteRowCol` above.
2. **All cofactors are equal.**  Every row and every column of `lapMatrix` sums to
   zero (`SimpleGraph.lapMatrix_mulVec_const_eq_zero` and its transpose), so adding
   all other rows to row `i` makes it the negation of row `j`; the standard
   determinant manipulation then equates cofactor `(i, j)` with cofactor `(i, i)`.
3. Combine, tracking the sign `(-1)^(i + j)`.

⚠ Step 2 is the whole content and is exactly what the principal case does not give.

**Formalisation.**  ⚠ Deleting row `i` and column `j` for `i ≠ j` leaves a matrix whose
row and column index types are the *different* subtypes `{v // v ≠ i}` and
`{v // v ≠ j}`, so `Matrix.det` does not apply to it.  A reindexing equiv `e` between
the two is therefore threaded through explicitly — the same device
`tau_eq_det_fromBlocks_K` uses further down this file for the same reason.  Because `e`
is not canonical it fixes the column order only up to a permutation, so the conclusion
is stated up to sign, absorbing `(-1)^(i+j)` and `sign e` together.  Taking `i = j` and
`e = Equiv.refl` recovers the principal case above.

⚠ Currently vacuous via `tau` and `IsConnectedDigraph`, exactly as the principal case
is. -/
theorem tau_eq_lapMatrix_cofactor
    (G : SimpleGraph V) [DecidableRel G.Adj] (hor : IsOrientationOf tail head G) (i j : V)
    (e : {v // v ≠ i} ≃ {v // v ≠ j}) :
    (tau tail head : ℤ) =
        ((G.lapMatrix ℤ).submatrix
          (fun v : {v // v ≠ i} => (v : V)) (fun v : {v // v ≠ i} => ((e v : V)))).det ∨
      (tau tail head : ℤ) =
        -((G.lapMatrix ℤ).submatrix
          (fun v : {v // v ≠ i} => (v : V)) (fun v : {v // v ≠ i} => ((e v : V)))).det := by
  sorry

-- Ex 12.2.3(b): the (unoriented) incidence matrix of a simple graph is totally unimodular ⟺ bipartite.
/-- **Exercise 12.2.3(b).**  *The incidence matrix of a simple graph `G` is totally
unimodular if and only if `G` is bipartite.*

**Book proof.**  None — an exercise.

**Skeleton** (for `(G.incMatrix ℤ).IsTotallyUnimodular ↔ G.IsBipartite`).
1. **(⇐).**  Given a bipartition, negate the rows on one side.  The `0/1` incidence
   matrix becomes a *signed* incidence matrix — each column then has one `+1` and one
   `-1` — which is totally unimodular by exercise 12.2.3(a) applied to any
   orientation.  Negating rows only changes signs of determinants, so total
   unimodularity transfers back.
2. **(⇒), contrapositive.**  If `G` is not bipartite it has an odd cycle (theorem
   1.2).  Take the submatrix on that cycle's vertices and edges: it is a circulant
   with two `1`s per column, and its determinant is `±2`.  Compute this directly for
   the `k`-cycle — the determinant of the `k × k` cyclic `0/1` matrix is
   `1 - (-1)^k`, which is `2` for odd `k` and `0` for even.
3. So total unimodularity fails, and the two directions give the `↔`.

**Reading.**  ⚠ Note this is the *unoriented* `0/1` incidence matrix of §1.3, **not**
the signed one of this chapter — the signed version is always totally unimodular, for
every graph.  The classical characterisation underlying the integrality of bipartite
matching linear programs, and it links back to theorem 1.2: bipartite means no odd
cycle.

**Formalisation.**  ★ Independent of every defective definition in this file — it
mentions only `SimpleGraph.incMatrix` and `IsBipartite`, both Mathlib.  Together with
exercise 12.2.2(a), one of the two items that can be filled today.  Step 2's
determinant computation is the concrete part. -/
theorem incMatrix_isTotallyUnimodular_iff_isBipartite
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.incMatrix ℤ).IsTotallyUnimodular ↔ G.IsBipartite := by
  sorry

-- Ex 12.2.4(b): dim(𝓑_F ∩ 𝓒_F) > 0 ⟺ p ∣ τ(G) (H. Shank) — the char-p self-orthogonality item.
/-- **Exercise 12.2.4(b)** (H. Shank).  *Let `F` be a field of characteristic `p`.
Then `dim(𝓑_F ∩ 𝓒_F) > 0` if and only if `p ∣ τ(G)`.*

**Book proof.**  None — an exercise, credited to H. Shank.

**Skeleton** (for `0 < finrank (𝓑_F ⊓ 𝓒_F) ↔ p ∣ τ(G)`).
1. **The stacked matrix `[B;C]` is square of size `ε`**, since
   `dim 𝓑 + dim 𝓒 = (ν-ω) + (ε-ν+ω) = ε` — corollary 12.2, valid over any field via
   the rank–nullity route.
2. **Its rows span `𝓑_F + 𝓒_F`**, being bases of the two summands.
3. **Singular ↔ the spaces meet.**  `ε` vectors spanning a space of dimension
   `dim(𝓑 + 𝓒) = dim 𝓑 + dim 𝓒 - dim(𝓑 ⊓ 𝓒) = ε - dim(𝓑 ⊓ 𝓒)` are dependent exactly
   when that intersection is nonzero.
4. **Part (a)** gives `det [B;C] = ±(τ : F)`, which vanishes exactly when
   `p ∣ τ(G)` (`ZMod`/`CharP.cast_eq_zero_iff`).
5. Chain 3 and 4.

**Reading.**  Over `ℝ` the two spaces are orthogonal complements and meet only in
zero.  In characteristic `p` the dot form is **degenerate** — a vector can be
orthogonal to itself — so they may genuinely overlap, and Shank's result says the
overlap is nontrivial exactly when `p ∣ τ(G)`.  A purely arithmetic property of
`τ(G)` detected by a linear-algebraic degeneracy — a striking illustration of the
chapter's theme.

**Formalisation.**  ⚠ Step 1 must **not** be derived from orthogonality (`dim 𝓒 =
ε - dim 𝓑`), which is exactly what fails here; use the rank–nullity argument
recorded under `finrank_cycleSpace`.  Getting this wrong would make the proof
circular — the whole point is that the two spaces are *not* complementary. -/
theorem finrank_inf_pos_iff_dvd_tau {p : ℕ} [Fact p.Prime] [CharP F p] :
    0 < Module.finrank F
        ((bondSpace tail head (F := F)) ⊓ (cycleSpace tail head (F := F)) :
          Submodule F (A → F)) ↔
      p ∣ tau tail head := by
  sorry

end CycleSpace
