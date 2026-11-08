/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.CircuitComplexity.StraightLine

/-!
# Straight-line programs for one and two inputs

For Boolean straight-line programs [AB09, Note 6.4] claims exactly that a function on
`n` bits has an `S`-line program iff it has an `S`-sized circuit (see [AB09, Ex 6.2]).
The program-to-circuit half is false, since [AB09, Def 6.1]'s size counts the `n` input
vertices and negated literals need `¬` gates (`exists_straightLine_and_not_dagCircuit`,
`StraightLine.lean`); the corrected statement, both directions within a factor `2` and an
additive `2n`, is proved (`exists_dagCircuit_of_straightLine`,
`exists_straightLine_of_dagCircuit`, `StraightLineDualRail.lean`).  This file proves the
circuit-to-program half with exactly `S` lines for `n ∈ {1, 2}`, by an exhaustive table
check (`decide`); for `n ≥ 3` it is not decided here.

## Main definitions

* `BoolCircuit.SLOperand.lit` — the literal operand `xᵢ` or `¬xᵢ`.
* `BoolCircuit.oneLine`, `BoolCircuit.Shape3` — one-line programs, and three-line programs
  `y₀ = a ∘ b; y₁ = c ∘ d; y₂ = y₀ ∘ y₁` over literals.
* `BoolCircuit.table1`, `BoolCircuit.table2` — a program of that shape for every function
  of one, resp. two, bits.

## Main results

* `BoolCircuit.exists_oneLine`, `BoolCircuit.exists_threeLine` — every function of one bit
  has a one-line program, every function of two bits a three-line program.
* `BoolCircuit.exists_straightLine_length_le_size_of_le_two` — the circuit-to-program
  direction of [AB09, Note 6.4] with the book's `S` lines, for `1 ≤ n ≤ 2`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Note 6.4, Exercise 6.2.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

open StraightLine

variable {n : ℕ}

/-- The literal operand `xᵢ` (if `b`) or `¬xᵢ` (if not `b`). -/
def SLOperand.lit (l : Fin n × Bool) : SLOperand n :=
  if l.2 then .input l.1 else .negInput l.1

/-- A literal operand may appear in any line. -/
theorem SLOperand.lit_before (l : Fin n × Bool) (i : ℕ) : (SLOperand.lit l).Before i := by
  unfold SLOperand.lit; split_ifs <;> trivial

/-- The literal `⟨i, b⟩` is true exactly when `xᵢ = b`. -/
theorem SLOperand.lit_eval (l : Fin n × Bool) (x : Fin n → Bool) (ys : List Bool) :
    (SLOperand.lit l).eval x ys = (x l.1 == l.2) := by
  rcases l with ⟨i, b⟩
  cases b <;> cases h : x i <;> simp [SLOperand.lit, SLOperand.eval, h]

/-- The parameters of a three-line program `y₀ = a ∘₁ b; y₁ = c ∘₂ d; y₂ = y₀ ∘₃ y₁` over
literals `a, b, c, d`. -/
structure Shape3 (n : ℕ) where
  /-- The operation of the first line. -/
  o1 : SLOp
  /-- The first operand of the first line. -/
  l1 : Fin n × Bool
  /-- The second operand of the first line. -/
  l2 : Fin n × Bool
  /-- The operation of the second line. -/
  o2 : SLOp
  /-- The first operand of the second line. -/
  l3 : Fin n × Bool
  /-- The second operand of the second line. -/
  l4 : Fin n × Bool
  /-- The operation of the third line, combining the first two. -/
  o3 : SLOp

/-- The statements of a `Shape3` program. -/
def Shape3.stmts (p : Shape3 n) : List (SLStmt n) :=
  [⟨p.o1, .lit p.l1, .lit p.l2⟩, ⟨p.o2, .lit p.l3, .lit p.l4⟩, ⟨p.o3, .line 0, .line 1⟩]

/-- A `Shape3` program reads only literals and earlier lines. -/
theorem Shape3.valid (p : Shape3 n) : LinesValid p.stmts := by
  intro i hi
  simp only [Shape3.stmts, List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · exact ⟨SLOperand.lit_before _ _, SLOperand.lit_before _ _⟩
  · exact ⟨SLOperand.lit_before _ _, SLOperand.lit_before _ _⟩
  · exact ⟨show 0 < 2 by omega, show 1 < 2 by omega⟩

/-- The program of a `Shape3`. -/
def Shape3.prog (p : Shape3 n) : StraightLineProgram n := ⟨p.stmts, p.valid⟩

/-- A `Shape3` program has three lines. -/
theorem Shape3.prog_length (p : Shape3 n) : p.prog.length = 3 := rfl

/-- A `Shape3` program outputs `(a ∘₁ b) ∘₃ (c ∘₂ d)`. -/
theorem Shape3.prog_eval (p : Shape3 n) (x : Fin n → Bool) :
    p.prog.eval x = p.o3.apply (p.o1.apply (x p.l1.1 == p.l1.2) (x p.l2.1 == p.l2.2))
      (p.o2.apply (x p.l3.1 == p.l3.2) (x p.l4.1 == p.l4.2)) := by
  simp only [StraightLineProgram.eval, StraightLineProgram.values, Shape3.prog_length]
  simp only [Shape3.prog, Shape3.stmts, runLines, List.foldl_cons, List.foldl_nil, SLStmt.eval,
    SLOperand.lit_eval]
  simp [SLOperand.eval]

/-- A one-line program `y₀ = a ∘ b` over literals. -/
def oneLine (o : SLOp) (l1 l2 : Fin n × Bool) : StraightLineProgram n :=
  ⟨[⟨o, .lit l1, .lit l2⟩], fun i hi => by
    simp only [List.length_cons, List.length_nil] at hi
    obtain rfl : i = 0 := by omega
    exact ⟨SLOperand.lit_before _ _, SLOperand.lit_before _ _⟩⟩

/-- A one-line program has one line. -/
theorem oneLine_length (o : SLOp) (l1 l2 : Fin n × Bool) : (oneLine o l1 l2).length = 1 := rfl

/-- A one-line program outputs `a ∘ b`. -/
theorem oneLine_eval (o : SLOp) (l1 l2 : Fin n × Bool) (x : Fin n → Bool) :
    (oneLine o l1 l2).eval x = o.apply (x l1.1 == l1.2) (x l2.1 == l2.2) := by
  simp only [StraightLineProgram.eval, StraightLineProgram.values, oneLine_length]
  simp only [oneLine, runLines, List.foldl_cons, List.foldl_nil, SLStmt.eval, SLOperand.lit_eval]
  simp

/-- A one-line program for each function of one bit, `f(0) = a`, `f(1) = b`. -/
def table1 : Bool → Bool → SLOp × (Fin 1 × Bool) × (Fin 1 × Bool)
  | false, false => (.and, ⟨0, true⟩, ⟨0, false⟩)
  | false, true => (.and, ⟨0, true⟩, ⟨0, true⟩)
  | true, false => (.and, ⟨0, false⟩, ⟨0, false⟩)
  | true, true => (.or, ⟨0, true⟩, ⟨0, false⟩)

/-- A three-line program for each function of two bits, given by its values at
`(x₀, x₁) = 00, 10, 01, 11`. -/
def table2 : Bool → Bool → Bool → Bool → Shape3 2
  | false, false, false, false => ⟨.and, ⟨0, true⟩, ⟨0, true⟩, .and, ⟨0, true⟩, ⟨0, false⟩, .and⟩
  | false, false, false, true => ⟨.and, ⟨0, true⟩, ⟨0, true⟩, .and, ⟨0, true⟩, ⟨1, true⟩, .and⟩
  | false, false, true, false => ⟨.and, ⟨0, false⟩, ⟨0, false⟩, .and, ⟨0, false⟩, ⟨1, true⟩, .and⟩
  | false, false, true, true => ⟨.and, ⟨1, true⟩, ⟨1, true⟩, .and, ⟨1, true⟩, ⟨1, true⟩, .and⟩
  | false, true, false, false => ⟨.and, ⟨0, true⟩, ⟨0, true⟩, .and, ⟨0, true⟩, ⟨1, false⟩, .and⟩
  | false, true, false, true => ⟨.and, ⟨0, true⟩, ⟨0, true⟩, .and, ⟨0, true⟩, ⟨0, true⟩, .and⟩
  | false, true, true, false => ⟨.and, ⟨0, true⟩, ⟨1, false⟩, .and, ⟨0, false⟩, ⟨1, true⟩, .or⟩
  | false, true, true, true => ⟨.and, ⟨0, true⟩, ⟨0, true⟩, .and, ⟨0, false⟩, ⟨1, true⟩, .or⟩
  | true, false, false, false => ⟨.and, ⟨0, false⟩, ⟨0, false⟩, .and, ⟨0, false⟩, ⟨1, false⟩, .and⟩
  | true, false, false, true => ⟨.and, ⟨0, true⟩, ⟨1, true⟩, .and, ⟨0, false⟩, ⟨1, false⟩, .or⟩
  | true, false, true, false => ⟨.and, ⟨0, false⟩, ⟨0, false⟩, .and, ⟨0, false⟩, ⟨0, false⟩, .and⟩
  | true, false, true, true => ⟨.and, ⟨0, true⟩, ⟨1, true⟩, .and, ⟨0, false⟩, ⟨0, false⟩, .or⟩
  | true, true, false, false => ⟨.and, ⟨1, false⟩, ⟨1, false⟩, .and, ⟨1, false⟩, ⟨1, false⟩, .and⟩
  | true, true, false, true => ⟨.and, ⟨0, true⟩, ⟨0, true⟩, .and, ⟨0, false⟩, ⟨1, false⟩, .or⟩
  | true, true, true, false => ⟨.and, ⟨0, true⟩, ⟨1, false⟩, .and, ⟨0, false⟩, ⟨0, false⟩, .or⟩
  | true, true, true, true => ⟨.and, ⟨0, true⟩, ⟨0, true⟩, .and, ⟨0, false⟩, ⟨0, false⟩, .or⟩

/-- Every Boolean function of one bit has a one-line program. -/
theorem exists_oneLine (f : (Fin 1 → Bool) → Bool) :
    ∃ P : StraightLineProgram 1, P.length = 1 ∧ ∀ x, P.eval x = f x := by
  set t := table1 (f fun _ => false) (f fun _ => true)
  refine ⟨oneLine t.1 t.2.1 t.2.2, rfl, fun x => ?_⟩
  rw [oneLine_eval]
  have hx : x = fun _ => x 0 := funext fun i => by rw [Subsingleton.elim i 0]
  have key : ∀ a b x0 : Bool, (table1 a b).1.apply (x0 == (table1 a b).2.1.2)
      (x0 == (table1 a b).2.2.2) = if x0 then b else a := by decide
  have h1 : ∀ a b, ((table1 a b).2.1.1 : Fin 1) = 0 := fun _ _ => Subsingleton.elim _ _
  have h2 : ∀ a b, ((table1 a b).2.2.1 : Fin 1) = 0 := fun _ _ => Subsingleton.elim _ _
  rw [h1, h2, key]
  conv_rhs => rw [hx]
  cases x 0 <;> rfl

/-- Every Boolean function of two bits has a three-line program. -/
theorem exists_threeLine (f : (Fin 2 → Bool) → Bool) :
    ∃ P : StraightLineProgram 2, P.length = 3 ∧ ∀ x, P.eval x = f x := by
  set p := table2 (f ![false, false]) (f ![true, false]) (f ![false, true]) (f ![true, true])
  refine ⟨p.prog, rfl, fun x => ?_⟩
  rw [Shape3.prog_eval]
  have hx : x = ![x 0, x 1] := funext fun i => by fin_cases i <;> rfl
  have key : ∀ a b c d x0 x1 : Bool,
      (table2 a b c d).o3.apply
        ((table2 a b c d).o1.apply (![x0, x1] (table2 a b c d).l1.1 == (table2 a b c d).l1.2)
          (![x0, x1] (table2 a b c d).l2.1 == (table2 a b c d).l2.2))
        ((table2 a b c d).o2.apply (![x0, x1] (table2 a b c d).l3.1 == (table2 a b c d).l3.2)
          (![x0, x1] (table2 a b c d).l4.1 == (table2 a b c d).l4.2)) =
      if x1 then (if x0 then d else c) else (if x0 then b else a) := by decide
  rw [hx, key]
  cases x 0 <;> cases x 1 <;> rfl

/-- **`S` lines suffice for `n ≤ 2`.**  For `n ∈ {1, 2}`, every circuit of the book's model
with `S` vertices has an equivalent straight-line program of at most `S` lines.
[AB09, Note 6.4, Ex 6.2], circuit-to-program direction, for one and two inputs.

No fan-in or well-formedness hypothesis is needed.

**Proof sketch.** If the output is an input `xᵢ`, the one line `xᵢ ∧ xᵢ` computes it and
`S ≥ n ≥ 1`.  Otherwise the circuit has a gate, so `S ≥ n + 1`, and every function of one
bit has a one-line program and every function of two bits a three-line program
(`exists_oneLine`, `exists_threeLine`, found by table lookup and checked by `decide`). -/
theorem exists_straightLine_length_le_size_of_le_two (h1 : 1 ≤ n) (h2 : n ≤ 2)
    (C : DAGCircuit n) :
    ∃ P : StraightLineProgram n, P.length ≤ C.size ∧ ∀ x, P.eval x = C.eval x := by
  by_cases ho : C.output < n
  · refine ⟨oneLine .and ⟨⟨C.output, ho⟩, true⟩ ⟨⟨C.output, ho⟩, true⟩, ?_, fun x => ?_⟩
    · rw [oneLine_length]; simp only [DAGCircuit.size]; omega
    · rw [oneLine_eval, DAGCircuit.eval]
      have := C.values_getD_input x ⟨C.output, ho⟩
      simp only at this
      rw [this]
      cases x ⟨C.output, ho⟩ <;> rfl
  · have hg : n + 1 ≤ C.size := by
      have := C.output_lt; simp only [DAGCircuit.size]; omega
    rcases (by omega : n = 1 ∨ n = 2) with rfl | rfl
    · obtain ⟨P, hP, hPe⟩ := exists_oneLine C.eval
      exact ⟨P, by omega, hPe⟩
    · obtain ⟨P, hP, hPe⟩ := exists_threeLine C.eval
      exact ⟨P, by omega, hPe⟩

end BoolCircuit
