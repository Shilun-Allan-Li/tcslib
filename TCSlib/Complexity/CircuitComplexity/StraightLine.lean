/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.TreeDAG

/-!
# Straight-line programs

Boolean straight-line programs, [AB09, Note 6.4]: a program of length `T` over inputs
`x₁, …, xₙ` is a list of statements `yᵢ = zᵢ₁ OP zᵢ₂` (`OP ∈ {∨, ∧}`), each operand being an
input, a negated input, or an earlier `yⱼ` (`j < i`).  The statements are executed in order
and the output is `y_T`.  This file defines the programs, compiles them into the book's
circuit model `BoolCircuit.DAGCircuit` ([AB09, Def 6.1]; the program-to-circuit half of
[AB09, Ex 6.2]), and formalizes the XOR example of [AB09, Figure 6.1 / Note 6.4].  The
circuit-to-program half and the two-sided statement of [AB09, Ex 6.2] are in
`StraightLineDualRail.lean`.

## Main definitions

* `BoolCircuit.SLOperand`, `BoolCircuit.SLOp`, `BoolCircuit.SLStmt` — operands, operations
  and statements of a straight-line program.
* `BoolCircuit.StraightLineProgram n` — a program over `n` inputs, with `length`, `values`
  and `eval`.
* `BoolCircuit.StraightLineProgram.toCircuit` — the circuit of a program.
* `BoolCircuit.xorCircuit`, `BoolCircuit.xorProgram` — [AB09, Figure 6.1 / Note 6.4].

## Main results

* `BoolCircuit.StraightLineProgram.toCircuit_eval`, `toCircuit_isFaninTwo`,
  `toCircuit_size` — a `T`-line program becomes a fan-in-two circuit of size
  `2n + max T 1`.
* `BoolCircuit.exists_straightLine_and_not_dagCircuit` — the literal program-to-circuit
  claim "`S` lines ⇒ size `S`" fails: `x₁ ∧ x₂` has a `1`-line program but no circuit of
  size `≤ 2`.
* `BoolCircuit.StraightLineProgram.eval_of_zero` — on zero inputs every program outputs `0`.
* `BoolCircuit.xorCircuit_eval`, `xorCircuit_isFaninTwo`, `xorCircuit_size`,
  `xorProgram_eval`, `xorProgram_length`.

## Divergences from [AB09, Note 6.4]

* **The empty program outputs `0`.**  [AB09] does not say what `y_T` is for `T = 0`; we read
  it as `0` (an `∨` of nothing).  With `n = 0` the grammar admits *only* the empty program
  (a first statement has no input and no earlier line to read), so the only function on
  zero inputs that a program computes is the constant `0`.
* **Size of the compiled circuit.**  [AB09] claims an `S`-line program gives an `S`-sized
  circuit.  Taken literally this is false: `x₁ ∧ x₂` is a `1`-line program, but every
  circuit computing it has size at least `3`, since size counts the `2` input vertices
  (`exists_straightLine_and_not_dagCircuit`).  So the `2n` term below is a genuine
  correction, not an artifact of the construction.  We get size `2n + max T 1`: `n`
  inputs, `n` negation gates (negating an input is free in a program but costs a `¬` gate
  in a circuit), one gate per line, and one constant gate for the empty program.
* **Figure 6.1's program.**  The program listed in [AB09, Note 6.4] starts with
  `y₁ = ¬x₁; y₂ = ¬x₂`, which is not in the book's own grammar (a statement must have a
  binary `∨`/`∧`, and negation is allowed only on input operands).  We use the in-grammar
  program `y₁ = ¬x₁ ∧ x₂; y₂ = x₁ ∧ ¬x₂; y₃ = y₁ ∨ y₂`.
* **Indexing.**  Lines and inputs are numbered from `0`: line `i` is the book's `y_{i+1}`,
  input `k` the book's `x_{k+1}`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Figure 6.1, Note 6.4, Exercise 6.2.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

/-! ## Programs -/

/-- An operand of a statement: an input `x_k`, a negated input `¬x_k`, or the value `y_j` of
an earlier line.  [AB09, Note 6.4] -/
inductive SLOperand (n : ℕ) where
  /-- The input variable `x_k`. -/
  | input (k : Fin n)
  /-- The negated input variable `¬x_k`. -/
  | negInput (k : Fin n)
  /-- The value of line `j` (the book's `y_{j+1}`). -/
  | line (j : ℕ)
  deriving DecidableEq, Repr

/-- The operation of a statement: `∧` or `∨`.  [AB09, Note 6.4] -/
inductive SLOp where
  /-- Conjunction `∧`. -/
  | and
  /-- Disjunction `∨`. -/
  | or
  deriving DecidableEq, Repr

/-- A statement `y = left OP right`.  [AB09, Note 6.4] -/
structure SLStmt (n : ℕ) where
  /-- The operation `OP`. -/
  op : SLOp
  /-- The first operand. -/
  left : SLOperand n
  /-- The second operand. -/
  right : SLOperand n
  deriving DecidableEq, Repr

variable {n : ℕ}

/-- The Boolean function of an operation. -/
def SLOp.apply : SLOp → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or, a, b => a || b

/-- The De Morgan dual of an operation: `∧ ↔ ∨`. -/
def SLOp.dual : SLOp → SLOp
  | .and => .or
  | .or => .and

/-- The gate label of an operation. -/
def SLOp.kind : SLOp → GateKind
  | .and => .and
  | .or => .or

namespace SLOperand

/-- The operand may appear in line `i`: it is an input, a negated input, or a line `j < i`. -/
def Before : SLOperand n → ℕ → Prop
  | line j, i => j < i
  | input _, _ => True
  | negInput _, _ => True

/-- The value of the operand on input `x`, line `j` holding `ys.getD j false`. -/
def eval (x : Fin n → Bool) (ys : List Bool) : SLOperand n → Bool
  | input k => x k
  | negInput k => !x k
  | line j => ys.getD j false

/-- An operand that may appear in line `i` may appear in any later line `j ≥ i`. -/
theorem Before.mono {o : SLOperand n} {i j : ℕ} (h : o.Before i) (hij : i ≤ j) :
    o.Before j := by
  cases o <;> simp_all [Before]; omega

/-- An operand reading only lines below `ys.length` ignores lines appended later. -/
theorem eval_append (x : Fin n → Bool) {o : SLOperand n} {ys : List Bool}
    (h : o.Before ys.length) (ext : List Bool) : o.eval x (ys ++ ext) = o.eval x ys := by
  cases o with
  | line j => exact List.getD_append _ _ _ _ h
  | input k => rfl
  | negInput k => rfl

end SLOperand

/-- The value of a statement, the earlier lines holding `ys`. -/
def SLStmt.eval (s : SLStmt n) (x : Fin n → Bool) (ys : List Bool) : Bool :=
  s.op.apply (s.left.eval x ys) (s.right.eval x ys)

/-- The statement may be line `i`: both operands are inputs or lines below `i`. -/
def SLStmt.Before (s : SLStmt n) (i : ℕ) : Prop :=
  s.left.Before i ∧ s.right.Before i

namespace StraightLine

/-- Every statement reads only inputs and earlier lines. -/
def LinesValid (ss : List (SLStmt n)) : Prop :=
  ∀ (i : ℕ) (h : i < ss.length), ss[i].Before i

/-- The empty statement list is valid. -/
theorem LinesValid.nil : LinesValid ([] : List (SLStmt n)) := fun i h => absurd h (by simp)

/-- Appending a statement that reads only inputs and existing lines keeps a statement
list valid. -/
theorem LinesValid.snoc {ss : List (SLStmt n)} (h : LinesValid ss) {s : SLStmt n}
    (hs : s.Before ss.length) : LinesValid (ss ++ [s]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
  · rw [List.getElem_append_left hlt]; exact h i hlt
  · simpa using hs

/-- Execute statements in order: the values `y₁, …, y_T` of all lines on input `x`. -/
def runLines (ss : List (SLStmt n)) (x : Fin n → Bool) : List Bool :=
  ss.foldl (fun ys s => ys ++ [s.eval x ys]) []

/-- Executing no statements gives no line values. -/
@[simp] theorem runLines_nil (x : Fin n → Bool) : runLines ([] : List (SLStmt n)) x = [] := rfl

/-- Executing one more statement appends its value, computed from the earlier lines. -/
theorem runLines_snoc (ss : List (SLStmt n)) (s : SLStmt n) (x : Fin n → Bool) :
    runLines (ss ++ [s]) x = runLines ss x ++ [s.eval x (runLines ss x)] := by
  simp [runLines, List.foldl_append]

/-- Executing `T` statements gives `T` line values. -/
@[simp] theorem length_runLines (ss : List (SLStmt n)) (x : Fin n → Bool) :
    (runLines ss x).length = ss.length := by
  induction ss using List.reverseRecOn with
  | nil => rfl
  | append_singleton ss s ih => simp [runLines_snoc, ih]

end StraightLine

open StraightLine

/-- A Boolean straight-line program over `n` inputs: a list of statements, statement `i`
reading only inputs, negated inputs and lines `j < i`.  [AB09, Note 6.4] -/
structure StraightLineProgram (n : ℕ) where
  /-- The statements, in execution order. -/
  stmts : List (SLStmt n)
  /-- Statement `i` reads only lines `j < i`. -/
  valid : LinesValid stmts

namespace StraightLineProgram

variable (P : StraightLineProgram n)

/-- The length `T` of the program: its number of statements.  [AB09, Note 6.4] -/
def length : ℕ := P.stmts.length

/-- The values of all lines on input `x`, computed by executing the statements in order. -/
def values (x : Fin n → Bool) : List Bool := runLines P.stmts x

/-- The output of the program: the value of the last line `y_T`, or `0` for the empty
program.  [AB09, Note 6.4] -/
def eval (x : Fin n → Bool) : Bool := (P.values x).getD (P.length - 1) false

/-- On zero inputs every program is empty, so it outputs `0`: a first statement would have
no input and no earlier line to read. -/
theorem eval_of_zero (P : StraightLineProgram 0) (x : Fin 0 → Bool) : P.eval x = false := by
  have hnil : P.stmts = [] := by
    rcases h : P.stmts with _ | ⟨s, ss⟩
    · rfl
    · have := (P.valid 0 (by simp [h])).1
      simp only [h, List.getElem_cons_zero] at this
      rcases s with ⟨_, l, _⟩
      cases l with
      | input k => exact k.elim0
      | negInput k => exact k.elim0
      | line j => exact absurd this (Nat.not_lt_zero j)
  simp [eval, values, length, hnil]

end StraightLineProgram

/-! ## From programs to circuits -/

/-- The circuit vertex holding an operand: input `k` is vertex `k`, its negation is the
`¬` gate at vertex `n + k`, and line `j` is the gate at vertex `2n + j`. -/
def SLOperand.vertex : SLOperand n → ℕ
  | input k => k
  | negInput k => n + k
  | line j => 2 * n + j

/-- The gate of a statement, reading the vertices of its operands (once, if they agree, to
keep the circuit free of parallel edges). -/
def SLStmt.toGate (s : SLStmt n) : DAGGate :=
  ⟨s.op.kind, if s.left.vertex = s.right.vertex then [s.left.vertex]
    else [s.left.vertex, s.right.vertex]⟩

namespace StraightLine

/-- The `n` negation gates `¬x_0, …, ¬x_{n-1}`, gate `k` at vertex `n + k`. -/
def negGates (n : ℕ) : List DAGGate := (List.range n).map fun k => ⟨.not, [k]⟩

/-- The negation gates followed by the gates of the statements. -/
def slpGates (ss : List (SLStmt n)) : List DAGGate := negGates n ++ ss.map SLStmt.toGate

/-- There are `n` negation gates. -/
@[simp] theorem length_negGates : (negGates n).length = n := by simp [negGates]

/-- The gates of a `T`-line program, before padding, number `n + T`. -/
@[simp] theorem length_slpGates (ss : List (SLStmt n)) :
    (slpGates ss).length = n + ss.length := by simp [slpGates]

/-- One more statement appends one more gate. -/
theorem slpGates_snoc (ss : List (SLStmt n)) (s : SLStmt n) :
    slpGates (ss ++ [s]) = slpGates ss ++ [s.toGate] := by simp [slpGates]

/-- The gate of a statement applies the statement's operation to the values of its operand
vertices. -/
theorem _root_.BoolCircuit.SLStmt.toGate_eval (s : SLStmt n) (vals : List Bool) :
    s.toGate.eval vals =
      s.op.apply (vals.getD s.left.vertex false) (vals.getD s.right.vertex false) := by
  unfold SLStmt.toGate
  split_ifs with h
  · rw [← h]; cases s.op <;> simp [DAGGate.eval, SLOp.apply, SLOp.kind]
  · cases s.op <;> simp [DAGGate.eval, SLOp.apply, SLOp.kind]

/-- The negation gates read only the input vertices. -/
theorem negGates_acyclic : GatesAcyclic n (negGates n) := by
  intro i hi a ha
  simp only [negGates, List.getElem_map, List.getElem_range, List.mem_singleton] at ha
  simp only [length_negGates] at hi
  omega

/-- The vertex of an operand that may appear in line `i` lies below the gate of line `i`,
vertex `2n + i`. -/
theorem _root_.BoolCircuit.SLOperand.vertex_lt {o : SLOperand n} {i : ℕ} (h : o.Before i) :
    o.vertex < 2 * n + i := by
  cases o with
  | input k => simp only [SLOperand.vertex]; omega
  | negInput k => simp only [SLOperand.vertex]; omega
  | line j => simp only [SLOperand.vertex, SLOperand.Before] at h ⊢; omega

/-- The gates of a valid program read only earlier vertices. -/
theorem slpGates_acyclic {ss : List (SLStmt n)} (h : LinesValid ss) :
    GatesAcyclic n (slpGates ss) := by
  induction ss using List.reverseRecOn with
  | nil => simpa [slpGates] using negGates_acyclic
  | append_singleton ss s ih =>
    have hv : LinesValid ss := fun i hi => by
      have := h i (by simp; omega); rwa [List.getElem_append_left hi] at this
    have hs : s.Before ss.length := by simpa using h ss.length (by simp)
    rw [slpGates_snoc]
    refine (ih hv).snoc fun a ha => ?_
    have h1 := SLOperand.vertex_lt hs.1
    have h2 := SLOperand.vertex_lt hs.2
    simp only [SLStmt.toGate] at ha
    split_ifs at ha <;> simp at ha <;> rcases ha with rfl | rfl <;> simp <;> omega

/-- The negation gate of input `k` holds `¬x_k`. -/
theorem vertexValue_negGates (x : Fin n → Bool) (k : Fin n) :
    vertexValue (negGates n) x (n + k) = !x k := by
  have key := runWith_getD_gate DAGGate.eval (negGates n) (List.ofFn x)
    (i := k) (by simp) false
  simp only [List.length_ofFn] at key
  rw [vertexValue, key]
  simp only [negGates, List.getElem_map, List.getElem_range, DAGGate.eval, List.all_cons,
    List.all_nil, Bool.and_true]
  rw [runWith_getD_of_lt _ _ _ (by simp)]
  simp

/-- With the line vertices correct, every operand vertex holds the operand's value. -/
theorem vertexValue_operand {ss : List (SLStmt n)} (x : Fin n → Bool)
    (hB : ∀ j < ss.length, vertexValue (slpGates ss) x (2 * n + j) = (runLines ss x).getD j false)
    {o : SLOperand n} (ho : o.Before ss.length) :
    vertexValue (slpGates ss) x o.vertex = o.eval x (runLines ss x) := by
  cases o with
  | input k => exact vertexValue_input _ x k
  | negInput k =>
    simp only [SLOperand.vertex, SLOperand.eval, slpGates]
    rw [vertexValue_append _ _ _ (by simp), vertexValue_negGates]
  | line j => exact hB j ho

/-- In the circuit of a valid program, the gate of line `j` (vertex `2n + j`) holds the value
of line `j`.

**Proof sketch.** Induction on the program by appending one statement.  Old lines keep
their values (appending gates and lines changes nothing earlier).  The new line's gate
applies the statement's operation to the vertices of its operands; an input operand's
vertex holds `x_k`, a negated input's the `¬` gate `¬x_k`, and an earlier line's vertex the
line's value by the induction hypothesis. -/
theorem vertexValue_slpGates_line {ss : List (SLStmt n)} (h : LinesValid ss) (x : Fin n → Bool) :
    ∀ j < ss.length, vertexValue (slpGates ss) x (2 * n + j) = (runLines ss x).getD j false := by
  induction ss using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton ss s ih =>
    have hv : LinesValid ss := fun i hi => by
      have := h i (by simp; omega); rwa [List.getElem_append_left hi] at this
    have hs : s.Before ss.length := by simpa using h ss.length (by simp)
    have ih' := ih hv
    intro j hj
    rw [List.length_append, List.length_singleton] at hj
    rw [slpGates_snoc, runLines_snoc]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [vertexValue_append _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simpa)]
      exact ih' j hj
    · have hidx : 2 * n + ss.length = n + (slpGates ss).length := by simp; omega
      rw [hidx, vertexValue_last, List.getD_append_right _ _ _ _ (by simp)]
      simp only [length_runLines, Nat.sub_self, List.getD_cons_zero]
      rw [SLStmt.toGate_eval, SLStmt.eval]
      exact congrArg₂ _ (vertexValue_operand x ih' hs.1) (vertexValue_operand x ih' hs.2)

end StraightLine

namespace StraightLineProgram

variable (P : StraightLineProgram n)

/-- The circuit of a program: the `n` negation gates, one gate per statement, and, for the
empty program, a constant-`0` gate (an `∨` of fan-in `0`).  [AB09, Ex 6.2] -/
def toCircuit : DAGCircuit n where
  gates := slpGates P.stmts ++ if P.length = 0 then [constGate false] else []
  output := 2 * n + (P.length - 1)
  args_lt := by
    split_ifs with h
    · exact (slpGates_acyclic P.valid).snoc (by simp)
    · intro i hi a ha
      simp only [List.append_nil] at hi ha
      exact slpGates_acyclic P.valid i hi a ha
  output_lt := by
    simp only [List.length_append, length_slpGates]
    unfold length
    split_ifs with h <;> simp <;> omega

/-- The circuit of a program computes the same function.  [AB09, Ex 6.2] -/
theorem toCircuit_eval (x : Fin n → Bool) : P.toCircuit.eval x = P.eval x := by
  show vertexValue _ x _ = _
  simp only [toCircuit]
  split_ifs with h
  · have hnil : P.stmts = [] := List.eq_nil_of_length_eq_zero h
    have hidx : 2 * n + (P.length - 1) = n + (slpGates P.stmts).length := by
      simp [h, hnil]; omega
    rw [hidx, vertexValue_last]
    simp [eval, values, hnil]
  · rw [List.append_nil]
    exact vertexValue_slpGates_line P.valid x _ (by unfold length at h ⊢; omega)

/-- The circuit of a program has fan-in at most two (and is well formed).  [AB09, Def 6.1] -/
theorem toCircuit_isFaninTwo : P.toCircuit.IsFaninTwo := by
  have key : ∀ g ∈ P.toCircuit.gates,
      (g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)) ∧ g.args.length ≤ 2 := by
    intro g hg
    simp only [toCircuit, slpGates, negGates, List.mem_append, List.mem_map,
      List.mem_range] at hg
    rcases hg with (⟨k, _, rfl⟩ | ⟨s, _, rfl⟩) | hg
    · simp
    · simp only [SLStmt.toGate]
      split_ifs with h
      · cases s.op <;> simp [SLOp.kind]
      · cases s.op <;> simp [SLOp.kind, h]
    · split_ifs at hg <;> simp_all [constGate]
  exact ⟨fun g hg => (key g hg).1, fun g hg => (key g hg).2⟩

/-- The circuit of a `T`-line program has size `2n + max T 1`: `n` inputs, `n` negation
gates, one gate per line (one constant gate when `T = 0`).  [AB09, Ex 6.2] -/
theorem toCircuit_size : P.toCircuit.size = 2 * n + max P.length 1 := by
  simp only [DAGCircuit.size, toCircuit, List.length_append, length_slpGates]
  unfold length
  split_ifs with h <;> simp [h] <;> omega

end StraightLineProgram

/-- The literal program-to-circuit half of [AB09, Ex 6.2] ("an `S`-line program gives an
`S`-sized circuit") is false: `x₁ ∧ x₂` on two inputs is computed by a `1`-line program,
but by no circuit of size at most `2`, since a circuit's size counts its `2` input vertices
and a circuit with no gate outputs an input bit. -/
theorem exists_straightLine_and_not_dagCircuit :
    (∃ P : StraightLineProgram 2, P.length = 1 ∧ ∀ x, P.eval x = (x 0 && x 1)) ∧
      ¬ ∃ C : DAGCircuit 2, C.size ≤ 2 ∧ ∀ x, C.eval x = (x 0 && x 1) := by
  refine ⟨⟨⟨[⟨.and, .input 0, .input 1⟩], fun i hi => ?_⟩, rfl, fun x => rfl⟩, ?_⟩
  · obtain rfl : i = 0 := by simp at hi; omega
    exact ⟨trivial, trivial⟩
  · rintro ⟨C, hsize, hC⟩
    have hgates : C.gates.length = 0 := by simp only [DAGCircuit.size] at hsize; omega
    have hout := C.output_lt
    rw [hgates] at hout
    have key : ∀ x, C.eval x = x ⟨C.output, by omega⟩ := fun x =>
      C.values_getD_input x ⟨C.output, by omega⟩
    have hlt : C.output < 2 := by omega
    rcases (by omega : C.output = 0 ∨ C.output = 1) with h | h
    · have := (key fun i => decide (i = 0)).symm.trans (hC fun i => decide (i = 0))
      simp [h] at this
    · have := (key fun i => decide (i = 1)).symm.trans (hC fun i => decide (i = 1))
      simp [h] at this

/-! ## The XOR example: [AB09, Figure 6.1 / Note 6.4] -/

/-- The circuit of [AB09, Figure 6.1] computing XOR on two bits: vertices `0, 1` are the
inputs, then `¬x₁`, `¬x₂`, `¬x₁ ∧ x₂`, `x₁ ∧ ¬x₂`, and the output `∨` of the last two. -/
def xorCircuit : DAGCircuit 2 where
  gates := [⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.and, [2, 1]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [4, 5]⟩]
  output := 6
  args_lt := by decide
  output_lt := by decide

/-- The circuit of [AB09, Figure 6.1] outputs `1` iff `x₁ ≠ x₂`. -/
theorem xorCircuit_eval (x : Fin 2 → Bool) : xorCircuit.eval x = true ↔ x 0 ≠ x 1 := by
  simp only [DAGCircuit.eval, DAGCircuit.values, xorCircuit, runWith, DAGGate.eval,
    List.ofFn_succ, List.ofFn_zero]
  have h1 : x (Fin.succ 0) = x 1 := rfl
  rw [h1]
  cases x 0 <;> cases x 1 <;> simp

/-- The circuit of [AB09, Figure 6.1] is well formed with fan-in at most two. -/
theorem xorCircuit_isFaninTwo : xorCircuit.IsFaninTwo := by
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩ <;>
    simp only [xorCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg <;>
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

/-- The circuit of [AB09, Figure 6.1] has size `7`: two inputs and five gates. -/
theorem xorCircuit_size : xorCircuit.size = 7 := rfl

/-- The straight-line program for XOR of [AB09, Note 6.4], in the book's grammar:
`y₁ = ¬x₁ ∧ x₂; y₂ = x₁ ∧ ¬x₂; y₃ = y₁ ∨ y₂`.  Deviation: [AB09] lists
`y₁ = ¬x₁; y₂ = ¬x₂; y₃ = y₁ ∧ x₂; y₄ = x₁ ∧ y₂; y₅ = y₃ ∨ y₄`, whose first two statements
are unary negations, outside the grammar of [AB09, Note 6.4]. -/
def xorProgram : StraightLineProgram 2 where
  stmts := [⟨.and, .negInput 0, .input 1⟩, ⟨.and, .input 0, .negInput 1⟩,
    ⟨.or, .line 0, .line 1⟩]
  valid := by
    intro i hi
    match i with
    | 0 => simp [SLStmt.Before, SLOperand.Before]
    | 1 => simp [SLStmt.Before, SLOperand.Before]
    | 2 => simp [SLStmt.Before, SLOperand.Before]
    | k + 3 => simp at hi

/-- The XOR program of [AB09, Note 6.4] (in-grammar version) outputs `1` iff `x₁ ≠ x₂`. -/
theorem xorProgram_eval (x : Fin 2 → Bool) : xorProgram.eval x = true ↔ x 0 ≠ x 1 := by
  simp only [StraightLineProgram.eval, StraightLineProgram.values, StraightLineProgram.length,
    xorProgram, runLines, List.foldl, SLStmt.eval, SLOperand.eval, SLOp.apply]
  cases x 0 <;> cases x 1 <;> simp

/-- The XOR program has `3` lines. -/
theorem xorProgram_length : xorProgram.length = 3 := rfl

end BoolCircuit
