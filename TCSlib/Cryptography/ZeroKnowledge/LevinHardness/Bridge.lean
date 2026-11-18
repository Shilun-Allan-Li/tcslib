/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.CircuitComplexity.DAGCircuitSat
import TCSlib.Complexity.NPReductions.ThreeSATToColoring
import TCSlib.Complexity.Formulas.CNFEncoding
import TCSlib.Cryptography.ZeroKnowledge.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reader bridge for frozen definitions without published readers (quarantined)

**Disclosed Rule-10 exception (user ruling on EF-H12's E-SCOPE, 2026-11-18: "readers in our
files").** The definitions below live in read-only files (`Complexity/**`, Arora–Barak and course
material) and publish no reader, so no consumer can read them without unfolding. This file states
each missing reader, with the content its owner would publish, proved by `rfl`/`Iff.rfl`; it is the
**only** place of `ZeroKnowledge/LevinHardness/` that sees through these definitions. Every
statement is a one-line reader to be moved, unchanged, into the owner file by an owner PR, after
which this file is deleted and its consumers re-pointed one-for-one (scope requests in the
delivery's `REPORT.md`).

| Reader | Definition | Owner file |
|---|---|---|
| `levinNPHard_iff` | `TCSlib.Cryptography.LevinNPHard` | `ZeroKnowledge/NP.lean:654` |
| `toCNF_eq` | `BoolCircuit.DAGCircuit.toCNF` | `CircuitComplexity/DAGCircuitSat.lean:267` |
| `widthAtMost_iff` | `Std.Sat.CNF.WidthAtMost` | `Formulas/CNF.lean:102` |
| `numVars_eq` | `CNF.numVars` | `Formulas/CNF.lean:96` |
| `serialize*_eq` (three) | `CNF.serialize*` | `Formulas/CNFEncoding.lean:99-110` |
| `decode_eq`, `fallback_eq` | `CNF.decode`, `fallback` | `CNFEncoding.lean:169-175` |
| `syntaxStep_eq`, `syntaxOK_eq` | `CNF.syntaxStep`, `syntaxOK` | `CNFEncoding.lean:608-723` |
| `satisfiesLiteral_pos`, `_neg` | `SATtoColor.SatisfiesLiteral` | `ThreeSATToColoring.lean` |
| `satisfiesClause_eq` | `SATtoColor.SatisfiesClause` | same |
| `satisfiesSat3_eq` | `SATtoColor.SatisfiesSat3` | same |
| `isSatisfiable_iff` | `SATtoColor.IsSatisfiable` | same |
| `is3Colorable_iff` | `SATtoColor.Is3Colorable` | same |
| `reductionGraph_adj` | `SATtoColor.ReductionGraph` | same |
| `edgeRelation_*` (case lemmas) | `SATtoColor.EdgeRelation` | same |

## Main results

The readers listed above (no new mathematics).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§6.1.2, Lemma 6.11.)
* CS 294-268 course material (UC Berkeley, Spring 2026, V. Guruswami), the 3SAT → 3-colouring
  reduction of `Complexity/NPReductions/ThreeSATToColoring.lean`.
-/

namespace TCSlib.Cryptography.LevinHardness.Bridge

open BoolCircuit SATtoColor Complexity
open Std.Sat (CNF)

/-! ### Levin NP-hardness -/

/-- Reader for `LevinNPHard` (missing in `ZeroKnowledge/NP.lean`): `(L', R')` is NP-hard with
Levin reductions iff every language with a witness relation has a Levin reduction to it,
`LevinNPHard L' R' ↔ ∀ L R, WitnessRelation L R → ∃ f w p, LevinReduction L L' R R' f w p`. -/
theorem levinNPHard_iff (L' : Language Bool) (R' : List Bool → List Bool → Prop) :
    LevinNPHard L' R' ↔ ∀ (L : Language Bool) (R : List Bool → List Bool → Prop),
      WitnessRelation L R → ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool)
        (p : PolyExpr), LevinReduction L L' R R' f w p := Iff.rfl

/-! ### Circuits and formulas -/

/-- Reader for `DAGCircuit.toCNF` (missing in `DAGCircuitSat.lean`): the Tseitin formula is the
output clause followed by the gate clauses,
`C.toCNF = [(C.output, true)] :: tseitinGates n C.gates`. -/
theorem toCNF_eq {n : ℕ} (C : DAGCircuit n) :
    C.toCNF = [(C.output, true)] :: tseitinGates n C.gates := rfl

/-- Reader for `CNF.WidthAtMost` (missing in `Formulas/CNF.lean`):
`φ.WidthAtMost k ↔ ∀ C ∈ φ, C.length ≤ k`. -/
theorem widthAtMost_iff {α : Type} (φ : CNF α) (k : ℕ) :
    φ.WidthAtMost k ↔ ∀ C ∈ φ, C.length ≤ k := Iff.rfl

/-- Reader for `CNF.numVars` (missing in `Formulas/CNF.lean`): one plus the largest variable,
`φ.numVars = (φ.flatMap fun C => C.map fun ℓ => ℓ.1 + 1).foldr max 0`. -/
theorem numVars_eq (φ : CNF ℕ) :
    φ.numVars = (φ.flatMap fun C => C.map fun ℓ => ℓ.1 + 1).foldr max 0 := rfl

/-- Reader for `CNF.serializeLit` (missing in `Formulas/CNFEncoding.lean`):
`serializeLit ℓ = 1^{ℓ.1 + 1} ++ [0, ℓ.2]`. -/
theorem serializeLit_eq (ℓ : Std.Sat.Literal ℕ) :
    CNF.serializeLit ℓ = List.replicate (ℓ.1 + 1) true ++ [false, ℓ.2] := rfl

/-- Reader for `CNF.serializeClause`: `serializeClause C = C.flatMap serializeLit ++ [0]`. -/
theorem serializeClause_eq (C : CNF.Clause ℕ) :
    CNF.serializeClause C = C.flatMap CNF.serializeLit ++ [false] := rfl

/-- Reader for `CNF.serialize`: each clause prefixed by `1`, then a final `0`,
`serialize φ = (φ.flatMap fun C => true :: serializeClause C) ++ [0]`. -/
theorem serialize_eq (φ : CNF ℕ) :
    CNF.serialize φ =
      (φ.flatMap fun C => true :: CNF.serializeClause C) ++ [false] := rfl

/-- Reader for `CNF.decode`: `decode x = (parse x).getD fallback`. -/
theorem decode_eq (x : List Bool) : CNF.decode x = (CNF.parse x).getD CNF.fallback := rfl

/-- Reader for `CNF.fallback`: the fallback formula is the empty CNF, `fallback = []`. -/
theorem fallback_eq : CNF.fallback = [] := rfl

/-- Reader for `CNF.syntaxStep` (the six-state grammar automaton): from state `0` a `1` goes to
`1` and a `0` to `4`; from `1`, to `2` / `0`; from `2`, to `2` / `3`; from `3` always to `1`;
from `4` and `5` always to `5`. -/
theorem syntaxStep_eq (q : Fin 6) (b : Bool) :
    CNF.syntaxStep q b =
      if q.val = 0 then (if b then 1 else 4)
      else if q.val = 1 then (if b then 2 else 0)
      else if q.val = 2 then (if b then 2 else 3)
      else if q.val = 3 then 1 else 5 := by
  fin_cases q <;> cases b <;> rfl

/-- Reader for `CNF.syntaxOK`: `syntaxOK x = decide (x.foldl syntaxStep 0 = 4)`. -/
theorem syntaxOK_eq (x : List Bool) :
    CNF.syntaxOK x = decide (x.foldl CNF.syntaxStep 0 = 4) := rfl

/-! ### The course reduction 3SAT → 3COL -/

/-- Reader for `SatisfiesLiteral` on a positive literal: `SatisfiesLiteral a (pos v) = a v`. -/
theorem satisfiesLiteral_pos {V : Type} (a : V → Bool) (v : V) :
    SatisfiesLiteral a (SATtoColor.Literal.pos v) = a v := rfl

/-- Reader for `SatisfiesLiteral` on a negative literal: `SatisfiesLiteral a (neg v) = !a v`. -/
theorem satisfiesLiteral_neg {V : Type} (a : V → Bool) (v : V) :
    SatisfiesLiteral a (SATtoColor.Literal.neg v) = !a v := rfl

/-- Reader for `SatisfiesClause`: a clause is satisfied iff one of its three literals is,
`SatisfiesClause a c = (SatisfiesLiteral a c.l1 || SatisfiesLiteral a c.l2 ||
SatisfiesLiteral a c.l3)`. -/
theorem satisfiesClause_eq {V : Type} (a : V → Bool) (c : Clause V) :
    SatisfiesClause a c =
      (SatisfiesLiteral a c.l1 || SatisfiesLiteral a c.l2 || SatisfiesLiteral a c.l3) := rfl

/-- Reader for `SatisfiesSat3`: `SatisfiesSat3 a f = f.all (SatisfiesClause a)`. -/
theorem satisfiesSat3_eq {V : Type} (a : V → Bool) (f : Sat3 V) :
    SatisfiesSat3 a f = f.all (SatisfiesClause a) := rfl

/-- Reader for `IsSatisfiable`: `IsSatisfiable f ↔ ∃ a, SatisfiesSat3 a f = true`. -/
theorem isSatisfiable_iff {V : Type} (f : Sat3 V) :
    IsSatisfiable f ↔ ∃ a : V → Bool, SatisfiesSat3 a f = true := Iff.rfl

/-- Reader for `Is3Colorable`: `Is3Colorable G ↔ Nonempty (G.Coloring (Fin 3))`. -/
theorem is3Colorable_iff {V' : Type} (G : SimpleGraph V') :
    Is3Colorable G ↔ Nonempty (G.Coloring (Fin 3)) := Iff.rfl

/-- Reader for `ReductionGraph`: `u` and `v` are adjacent iff `u ≠ v` and the edge relation
holds in one of the two orientations. -/
theorem reductionGraph_adj {V : Type} (f : Sat3 V) (u v : OutputVertex V) :
    (ReductionGraph f).Adj u v ↔ u ≠ v ∧ (EdgeRelation f u v ∨ EdgeRelation f v u) := Iff.rfl

/-- `EdgeRelation`, palette–palette: `EdgeRelation f (palette i) (palette j) ↔ i ≠ j`. -/
theorem edgeRelation_palette_palette {V : Type} (f : Sat3 V) (i j : Fin 3) :
    EdgeRelation f (.palette i) (.palette j) ↔ i ≠ j := by
  fin_cases i <;> fin_cases j <;> simp [EdgeRelation]

/-- `EdgeRelation`, palette–literal: holds iff the palette vertex is the base `0`. -/
theorem edgeRelation_palette_literal {V : Type} (f : Sat3 V) (i : Fin 3) (l : Literal V) :
    EdgeRelation f (.palette i) (.literalNode l) ↔ i = 0 := by
  fin_cases i <;> simp [EdgeRelation]

/-- `EdgeRelation`, literal–palette: holds iff the palette vertex is the base `0`. -/
theorem edgeRelation_literal_palette {V : Type} (f : Sat3 V) (l : Literal V) (i : Fin 3) :
    EdgeRelation f (.literalNode l) (.palette i) ↔ i = 0 := by
  fin_cases i <;> cases l <;> simp [EdgeRelation]

/-- `EdgeRelation`, literal–literal: holds iff the two literals are a variable and its negation,
in either order. -/
theorem edgeRelation_literal_literal {V : Type} (f : Sat3 V) (l l' : Literal V) :
    EdgeRelation f (.literalNode l) (.literalNode l') ↔
      ∃ x, (l = .pos x ∧ l' = .neg x) ∨ (l = .neg x ∧ l' = .pos x) := by
  cases l <;> cases l' <;> simp [EdgeRelation, eq_comm]

/-- `EdgeRelation`, gadget–gadget: holds iff both nodes belong to the gadget of the same clause
of `f` and their indices are one of the fourteen ordered pairs of the gadget's edges. -/
theorem edgeRelation_gadget_gadget {V : Type} (f : Sat3 V) (c c' : Clause V) (i j : Fin 6) :
    EdgeRelation f (.clauseGadget c i) (.clauseGadget c' j) ↔
      c = c' ∧ c ∈ f ∧ ((i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨
        (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 4) ∨ (i = 3 ∧ j = 5) ∨ (i = 4 ∧ j = 5) ∨
        (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 2) ∨
        (i = 4 ∧ j = 3) ∨ (i = 5 ∧ j = 3) ∨ (i = 5 ∧ j = 4)) := by
  simp only [EdgeRelation]

/-- `EdgeRelation`, literal–gadget: the literal is the clause's first, second or third literal
and the gadget index is `0`, `1` or `4` respectively. -/
theorem edgeRelation_literal_gadget {V : Type} (f : Sat3 V) (z : Literal V) (c : Clause V)
    (i : Fin 6) :
    EdgeRelation f (.literalNode z) (.clauseGadget c i) ↔
      (z = c.l1 ∧ i = 0) ∨ (z = c.l2 ∧ i = 1) ∨ (z = c.l3 ∧ i = 4) := by
  cases z <;> rfl

/-- `EdgeRelation`, gadget–literal: as `edgeRelation_literal_gadget`, in the other orientation. -/
theorem edgeRelation_gadget_literal {V : Type} (f : Sat3 V) (c : Clause V) (i : Fin 6)
    (z : Literal V) :
    EdgeRelation f (.clauseGadget c i) (.literalNode z) ↔
      (z = c.l1 ∧ i = 0) ∨ (z = c.l2 ∧ i = 1) ∨ (z = c.l3 ∧ i = 4) := by
  cases z <;> fin_cases i <;> rfl

/-- `EdgeRelation`, gadget–palette: holds iff the gadget index is `5` and the palette vertex is
`0` or `2`. -/
theorem edgeRelation_gadget_palette {V : Type} (f : Sat3 V) (c : Clause V) (i : Fin 6)
    (p : Fin 3) :
    EdgeRelation f (.clauseGadget c i) (.palette p) ↔ i = 5 ∧ (p = 0 ∨ p = 2) := by
  fin_cases i <;> fin_cases p <;> simp [EdgeRelation]

/-- `EdgeRelation`, palette–gadget: holds iff the gadget index is `5` and the palette vertex is
`0` or `2`. -/
theorem edgeRelation_palette_gadget {V : Type} (f : Sat3 V) (p : Fin 3) (c : Clause V)
    (i : Fin 6) :
    EdgeRelation f (.palette p) (.clauseGadget c i) ↔ i = 5 ∧ (p = 0 ∨ p = 2) := by
  fin_cases i <;> fin_cases p <;> simp [EdgeRelation]

end TCSlib.Cryptography.LevinHardness.Bridge
