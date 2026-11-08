/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.MaxCutDefinitions
import TCSlib.Complexity.Formulas.CNFEncoding
import TCSlib.Complexity.ClassNP.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Encoded Unique Games and Max-Cut promise problems

## Main definitions

* `UniqueGameConstraint`: endpoints and an explicit permutation table.
* `encodeNatRows`, `parseNatRows`: transport the existing binary CNF codec.
* `parseUniqueGame`, `parseMaxCut`: validate finite edge/constraint lists.
* `uniqueGameOptimum`: the optimal satisfied constraint fraction.
* `maxCutGraph`: convert an edge list to the existing weighted graph model.
* `PolyTimePromiseReducible`, `PromiseNPHard`: use the existing machine-based
  `Complexity.PolyTimeComputable`, with distinct YES and NO promises.
* `UniqueGamesConjecture`: the usual arbitrarily small-gap conjecture.

## Main results

Definitions only. These give Theorem 11.74 a concrete computational meaning,
including binary input encoding and genuine polynomial-time reductions.
The codec is reused as a transport for natural-number rows; no new recursive
parser or machine interpreter is introduced. Repeated constraints represent
parallel edges. Malformed encodings and empty instances satisfy neither promise.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §7.3, Exercises 7.27 and 7.30(h), §11.7, Thm. 11.74.
* [AB09] S. Arora and B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, §2.2, polynomial-time many-one reductions.
-/

open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace.UniqueGames

open Hypercontractivity

/-- A Unique Games constraint requires `π(label(right)) = label(left)`, with π
stored as a finite table. [OD14, §7.3, Unique Games; §11.7, Thm. 11.74] -/
structure UniqueGameConstraint where
  /-- The first variable index. -/
  left : ℕ
  /-- The second variable index. -/
  right : ℕ
  /-- The permutation values in increasing input order. -/
  table : List ℕ
  deriving DecidableEq

/-- A loop-free q-label constraint has a table listing exactly a permutation of
the labels `0,...,q-1`. [OD14, §7.3, Unique Games] -/
def UniqueGameConstraint.Valid (q : ℕ) (e : UniqueGameConstraint) : Prop :=
  e.left ≠ e.right ∧ e.table.Perm (List.range q)

instance (q : ℕ) (e : UniqueGameConstraint) : Decidable (e.Valid q) :=
  inferInstanceAs (Decidable (e.left ≠ e.right ∧ e.table.Perm (List.range q)))

/-- Encode natural-number rows with the existing CNF codec, assigning true
polarity to every literal. This is only a change of input representation.
[OD14, §11.7, finite CSP inputs; AB09, §2.2] -/
def encodeNatRows (rows : List (List ℕ)) : List Bool :=
  Std.Sat.CNF.serialize (rows.map fun row => row.map fun k => (k, true))

/-- Decode natural-number rows through the existing exact-consumption CNF parser,
rejecting false-polarity literals. [OD14, §11.7, finite CSP inputs; AB09, §2.2] -/
def parseNatRows (bits : List Bool) : Option (List (List ℕ)) := do
  let φ ← Std.Sat.CNF.parse bits
  if φ.all (fun row => row.all fun lit => lit.2) then
    some (φ.map fun row => row.map fun lit => lit.1)
  else none

/-- Decode one row as a valid q-label permutation constraint.
[OD14, §7.3, Unique Games] -/
noncomputable def parseUniqueGameConstraint (q : ℕ) : List ℕ → Option UniqueGameConstraint
  | u :: v :: table =>
      let e : UniqueGameConstraint := ⟨u, v, table⟩
      if e.Valid q then some e else none
  | _ => none

/-- Decode an entire Unique Games instance, rejecting any invalid constraint.
[OD14, §7.3, Unique Games; §11.7, Thm. 11.74] -/
noncomputable def parseUniqueGame (q : ℕ) (bits : List Bool) :
    Option (List UniqueGameConstraint) := do
  let rows ← parseNatRows bits
  rows.mapM (parseUniqueGameConstraint q)

/-- Encode a finite Unique Games instance using its endpoints and tables.
[OD14, §7.3, Unique Games; §11.7, Thm. 11.74] -/
def encodeUniqueGame (G : List UniqueGameConstraint) : List Bool :=
  encodeNatRows (G.map fun e => e.left :: e.right :: e.table)

/-- Decode one row as a loop-free Max-Cut edge. [OD14, §11.7, Max-Cut] -/
def parseMaxCutEdge : List ℕ → Option (ℕ × ℕ)
  | [u, v] => if u ≠ v then some (u, v) else none
  | _ => none

/-- Decode a complete Max-Cut edge list, preserving repeated edges.
[OD14, §11.7, Max-Cut] -/
def parseMaxCut (bits : List Bool) : Option (List (ℕ × ℕ)) := do
  let rows ← parseNatRows bits
  rows.mapM parseMaxCutEdge

/-- Encode the Max-Cut edge list with the existing CNF-based row codec.
[OD14, §11.7, Max-Cut] -/
def encodeMaxCut (E : List (ℕ × ℕ)) : List Bool :=
  encodeNatRows (E.map fun e => [e.1, e.2])

/-- The fraction of Unique Games constraints satisfied by a total assignment.
Only the finitely many mentioned endpoints affect the value.
[OD14, §7.3, Unique Games] -/
noncomputable def uniqueGameAssignmentValue {q : ℕ}
    (G : List UniqueGameConstraint) (label : ℕ → Fin q) : ℝ :=
  ((G.filter fun e => decide (e.table[(label e.right).val]? =
    some (label e.left).val)).length : ℝ) / (G.length : ℝ)

/-- The optimal satisfied fraction for the encoded q-label Unique Games model.
[OD14, §7.3, Unique Games] Promises require nonempty input; the conjecture
additionally requires a positive alphabet size. -/
noncomputable def uniqueGameOptimum (q : ℕ) (G : List UniqueGameConstraint) : ℝ :=
  sSup (Set.range (uniqueGameAssignmentValue (q := q) G))

/-- The endpoint bound of an edge list reuses the existing CNF variable-count
function. [OD14, §11.7, finite Max-Cut input representation] -/
def maxCutVertexBound (E : List (ℕ × ℕ)) : ℕ :=
  Std.Sat.CNF.numVars (E.map fun e => [(e.1, true), (e.2, true)])

/-- An edge list as a normalized symmetric weighted graph. Both orientations
share the weight of each original edge. [OD14, §11.7, random-edge convention]
The objective is reused from `MaxCutDefinitions`, rather than redefined here. -/
noncomputable def maxCutGraph (E : List (ℕ × ℕ)) : WeightedDigraph (Fin (maxCutVertexBound E)) where
  graph := ⟨fun v w => (v.val, w.val) ∈ E ∨ (w.val, v.val) ∈ E⟩
  edgeWeight v w := ((E.count (v.val, w.val) + E.count (w.val, v.val) : ℕ) : ℝ) /
    (2 * (E.length : ℝ))

/-- YES instances of the q-label Unique Games β-completeness promise.
[OD14, §7.3, (α,β)-approximation convention] -/
def uniqueGameYes (q : ℕ) (β : ℝ) : Language Bool :=
  {bits | ∃ G, parseUniqueGame q bits = some G ∧ G ≠ [] ∧ β ≤ uniqueGameOptimum q G}

/-- NO instances have optimum strictly below the soundness threshold.
[OD14, §7.3, (α,β)-approximation convention]
The strict inequality keeps the YES and NO promises disjoint when α=β. -/
def uniqueGameNo (q : ℕ) (α : ℝ) : Language Bool :=
  {bits | ∃ G, parseUniqueGame q bits = some G ∧ G ≠ [] ∧ uniqueGameOptimum q G < α}

/-- YES instances of the Max-Cut β-completeness promise.
[OD14, §11.7, Thm. 11.74] -/
def maxCutYes (β : ℝ) : Language Bool :=
  {bits | ∃ E, parseMaxCut bits = some E ∧ E ≠ [] ∧ β ≤ MaxCut.optimum (maxCutGraph E)}

/-- NO instances of Max-Cut have optimum strictly below α.
[OD14, §11.7, Thm. 11.74] -/
def maxCutNo (α : ℝ) : Language Bool :=
  {bits | ∃ E, parseMaxCut bits = some E ∧ E ≠ [] ∧ MaxCut.optimum (maxCutGraph E) < α}

/-- A polynomial-time map preserves the YES and NO sides of a promise problem.
The computability predicate is the existing machine-based project definition.
[OD14, §7.3, approximation reductions; AB09, §2.2] -/
def PolyTimePromiseReducible (Y N Y' N' : Language Bool) : Prop :=
  ∃ f : List Bool → List Bool, Complexity.PolyTimeComputable f ∧
    (∀ x, x ∈ Y → f x ∈ Y') ∧ (∀ x, x ∈ N → f x ∈ N')

/-- A promise problem is NP-hard when every NP language reduces to its YES/NO
promises in polynomial time. [OD14, §7.3; AB09, §2.2] -/
def PromiseNPHard (Y N : Language Bool) : Prop :=
  Disjoint Y N ∧
    ∀ L : Language Bool, L ∈ Complexity.NP → PolyTimePromiseReducible L Lᶜ Y N

/-- The Unique Games Conjecture states that for every small positive gap tolerance
some positive alphabet size makes the corresponding Unique Games promise
NP-hard. [OD14, Ex. 7.27; §11.7, Thm. 11.74]
The range `(0,1/2)` is the nonoverlapping promise regime; larger tolerances give
no additional approximation requirement. Finite unweighted constraint lists,
including repetitions, fix the input model. -/
def UniqueGamesConjecture : Prop :=
  ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) (1 / 2) → ∃ q : ℕ, 0 < q ∧
    PromiseNPHard (uniqueGameYes q (1 - ε)) (uniqueGameNo q ε)

end BooleanAnalysis.GaussianSpace.UniqueGames
