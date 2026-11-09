/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.CircuitComplexity.CircuitEvalSpec
import TCSlib.Complexity.CircuitComplexity.DAGCircuitSat
import TCSlib.Complexity.Formulas.CNFEncoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Tseitin emitter: a streaming algorithm over circuit descriptions

The polynomial-time half of [AB09, Lem 6.11] needs a machine that reads the description
`DAGCircuit.encode C` of a fan-in-two circuit and writes the serialization
(`Std.Sat.CNF.serialize`) of the Tseitin clauses of its gates.  This file is the
machine-independent half: a one-pass algorithm over the description with three unary
counters — the current vertex `z` and the (at most two) arguments `a`, `b` of the
current gate — and the proof that it emits exactly
`CNF.serialize (tseitinGates n C.gates)`.  `CircuitSatReductionMachine.lean` implements
it as a three-work-tape Turing machine.

The algorithm reads the description bit by bit in a finite-control *phase*
(`BoolCircuit.CktSatReduction.Emitter.Ph`): it counts the number of inputs into `z`, then for
each gate reads its label and its arguments into `a` and `b`; at the end of the argument
list it emits the gate's clauses, resets `a`, `b` and advances `z`.  At the end of the
gate list it emits the formula terminator and stops.  The clauses of a gate are
emitted by a fixed *program* (`BoolCircuit.CktSatReduction.Emitter.prog`) of output bits and
"print counter `t` in unary" instructions, obtained by running `DAGGate.tseitin` on the
symbolic vertices `0, 1, 2`.

## Main definitions

* `BoolCircuit.CktSatReduction.Emitter.lstep` — the action of the algorithm on one input symbol.
* `BoolCircuit.CktSatReduction.Emitter.prog` — the emission program of a gate.
* `BoolCircuit.CktSatReduction.Emitter.emRun` — the output of the algorithm from a given state.
* `BoolCircuit.CktSatReduction.Emitter.gateClauses` — the algorithm's output from the start.

## Main results

* `BoolCircuit.CktSatReduction.Emitter.emitBits_eq` — the program of a gate prints the
  serialization of its Tseitin clauses.
* `BoolCircuit.CktSatReduction.Emitter.gateClauses_encode` — on the description of a circuit of
  fan-in at most two, the algorithm outputs `CNF.serialize (tseitinGates n C.gates)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1.2, Lemma 6.11, p. 111.)
-/

namespace BoolCircuit

namespace CktSatReduction

namespace Emitter

open Std.Sat (CNF)

/-! ## The finite control -/

/-- The phases of the emitter, each expecting the next description bit: counting the
number of inputs (`n`), expecting a gate or the end of the gate list (`g`), the two
label bits (`k1`, `k2`), expecting the next argument or the end of the argument list
having read `c` arguments (`l k c`), and inside the unary code of argument `c`
(`u k c`). -/
inductive Ph
  | n
  | g
  | k1
  | k2 (b : Bool)
  | l (k : GateKind) (c : Fin 3)
  | u (k : GateKind) (c : Fin 3)
  deriving DecidableEq, Fintype

/-- A logical action on one input symbol: halt (emitting at most one bit), go to a phase
(possibly incrementing counter `t`), or end a gate with label `k` and `c` arguments. -/
inductive LA
  | halt (o : Option Bool)
  | go (φ : Ph) (inc : Option (Fin 3))
  | gate (k : GateKind) (c : Fin 3)

/-- **The emitter on one input symbol** (`none`: the end of the input).  Counter `0` is
the vertex `z`, counters `1`, `2` are the arguments. -/
def lstep : Ph → Option Bool → LA
  | _, none => .halt none
  | .n, some true => .go .n (some 0)
  | .n, some false => .go .g none
  | .g, some true => .go .k1 none
  | .g, some false => .halt (some false)
  | .k1, some b => .go (.k2 b) none
  | .k2 b₁, some b₂ => .go (.l (CircuitEval.kindOf b₁ b₂) 0) none
  | .l k c, some true => if c = 2 then .halt none else .go (.u k c) none
  | .l k c, some false => .gate k c
  | .u k c, some true => .go (.u k c) (some (c + 1))
  | .u k c, some false => .go (.l k (c + 1)) none

/-! ## The emission program of a gate -/

/-- An emission instruction: output a bit, or print counter `t` in unary. -/
inductive Instr
  | out (b : Bool)
  | pr (t : Fin 3)

/-- A symbolic vertex as a counter index (symbolic vertices are `0, 1, 2`). -/
def vtx (v : ℕ) : Fin 3 := ⟨v % 3, Nat.mod_lt _ (by decide)⟩

/-- The instructions printing a literal over the symbolic vertices `0, 1, 2`: its vertex
in unary, then `1 0` and the polarity — `serializeLit` with the counter in place of
`v`. -/
def litProg (ℓ : Std.Sat.Literal ℕ) : List Instr :=
  [.pr (vtx ℓ.1), .out true, .out false, .out ℓ.2]

/-- The program printing a symbolic formula clause by clause, as `CNF.serialize` does
(without the final terminator). -/
def progOf (φ : CNF ℕ) : List Instr :=
  φ.flatMap fun C => .out true :: (C.flatMap litProg ++ [.out false])

/-- The symbolic argument list of a gate with `c` arguments. -/
def argsSym : Fin 3 → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1, 2]

/-- **The emission program** of a gate with label `k` and `c` arguments: the Tseitin
clauses of the gate at symbolic vertex `0` reading symbolic vertices `1, 2`. -/
def prog (k : GateKind) (c : Fin 3) : List Instr :=
  progOf (DAGGate.tseitin 0 ⟨k, argsSym c⟩)

/-- The bits an instruction prints, with counter values `v`. -/
def exec (v : Fin 3 → ℕ) : Instr → List Bool
  | .out b => [b]
  | .pr t => List.replicate (v t) true

/-- The bits printed by the emission program of a gate. -/
def emitBits (k : GateKind) (c : Fin 3) (v : Fin 3 → ℕ) : List Bool :=
  (prog k c).flatMap (exec v)

/-- The serialization of a formula without its terminator. -/
def serBody (φ : CNF ℕ) : List Bool :=
  φ.flatMap fun C => true :: CNF.serializeClause C

/-- `CNF.serialize` is the body followed by the terminator. -/
theorem serialize_eq_serBody (φ : CNF ℕ) : CNF.serialize φ = serBody φ ++ [false] := rfl

/-- The actual argument list of a gate with `c` arguments `a, b`. -/
def argsOf : Fin 3 → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | 1, a, _ => [a]
  | 2, a, b => [a, b]

/-- Running a symbolic program prints the serialization of the formula with each
symbolic vertex `t` replaced by the counter value `v t`. -/
theorem flatMap_exec_progOf (v : Fin 3 → ℕ) (φ : CNF ℕ) :
    (progOf φ).flatMap (exec v) =
      serBody (φ.map fun C => C.map fun ℓ => (v (vtx ℓ.1), ℓ.2)) := by
  have hC : ∀ C : CNF.Clause ℕ, (C.flatMap litProg).flatMap (exec v) =
      (C.map fun ℓ => (v (vtx ℓ.1), ℓ.2)).flatMap CNF.serializeLit := by
    intro C
    induction C with
    | nil => rfl
    | cons ℓ C ih =>
      simp only [List.flatMap_cons, List.flatMap_append, List.map_cons, ih]
      simp [litProg, exec, CNF.serializeLit, List.replicate_succ']
  induction φ with
  | nil => rfl
  | cons C φ ih =>
    simp only [progOf, List.flatMap_cons, List.flatMap_append] at ih ⊢
    rw [ih]
    simp [serBody, exec, CNF.serializeClause, hC]

/-- **The program of a gate prints its Tseitin clauses**: with counters `z, a, b`, the
emission program of label `k` and `c` arguments prints the serialization (without
terminator) of the clauses of the gate `⟨k, argsOf c a b⟩` at vertex `z`. -/
theorem emitBits_eq (k : GateKind) (c : Fin 3) (v : Fin 3 → ℕ) :
    emitBits k c v = serBody (DAGGate.tseitin (v 0) ⟨k, argsOf c (v 1) (v 2)⟩) := by
  rw [emitBits, prog, flatMap_exec_progOf]
  congr 1
  cases k <;> fin_cases c <;> rfl

/-- Every emission program has at most `56` instructions. -/
theorem length_prog_le (k : GateKind) (c : Fin 3) : (prog k c).length ≤ 56 := by
  cases k <;> fin_cases c <;> decide

/-! ## The abstract run -/

/-- The abstract state: the phase and the three counters (vertex `z`, arguments `a`,
`b`). -/
structure ES where
  /-- the phase -/
  φ : Ph
  /-- the current vertex -/
  z : ℕ
  /-- the first argument read so far -/
  a : ℕ
  /-- the second argument read so far -/
  b : ℕ

/-- The counters as a function of the counter index. -/
def ES.vec (s : ES) : Fin 3 → ℕ
  | 0 => s.z
  | 1 => s.a
  | 2 => s.b

/-- Increment counter `t` and go to phase `φ`. -/
def ES.incTo (s : ES) (φ : Ph) : Fin 3 → ES
  | 0 => ⟨φ, s.z + 1, s.a, s.b⟩
  | 1 => ⟨φ, s.z, s.a + 1, s.b⟩
  | 2 => ⟨φ, s.z, s.a, s.b + 1⟩

/-- Incrementing counter `t` updates the counter vector at `t`. -/
theorem ES.vec_incTo (s : ES) (φ : Ph) (t : Fin 3) :
    (s.incTo φ t).vec = Function.update s.vec t (s.vec t + 1) := by
  funext j
  fin_cases t <;> fin_cases j <;> rfl

/-- **The emitter's output** from state `s` on the remaining input. -/
def emRun : ES → List Bool → List Bool
  | _, [] => []
  | s, b :: l => match lstep s.φ (some b) with
    | .halt o => o.toList
    | .go φ' none => emRun ⟨φ', s.z, s.a, s.b⟩ l
    | .go φ' (some t) => emRun (s.incTo φ' t) l
    | .gate k c => emitBits k c s.vec ++ emRun ⟨.g, s.z + 1, 0, 0⟩ l

/-- **The emitter's string function**: its output on the whole input, from phase `n` with
all counters `0`. -/
def gateClauses (w : List Bool) : List Bool := emRun ⟨.n, 0, 0, 0⟩ w

/-! ## Correctness on circuit descriptions -/

private theorem emRun_n (z k : ℕ) (r : List Bool) :
    emRun ⟨.n, z, 0, 0⟩ (List.replicate k true ++ r) = emRun ⟨.n, z + k, 0, 0⟩ r := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, emRun, lstep]
    rw [show (ES.incTo ⟨.n, z, 0, 0⟩ .n 0) = ⟨.n, z + 1, 0, 0⟩ from rfl, ih]
    congr 2
    omega

private theorem emRun_u0 (k : GateKind) (z a j : ℕ) (r : List Bool) :
    emRun ⟨.u k 0, z, a, 0⟩ (List.replicate j true ++ r) =
      emRun ⟨.u k 0, z, a + j, 0⟩ r := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, emRun, lstep]
    rw [show (ES.incTo ⟨.u k 0, z, a, 0⟩ (.u k 0) (0 + 1)) = ⟨.u k 0, z, a + 1, 0⟩ from rfl,
      ih]
    congr 2
    omega

private theorem emRun_u1 (k : GateKind) (z a b j : ℕ) (r : List Bool) :
    emRun ⟨.u k 1, z, a, b⟩ (List.replicate j true ++ r) =
      emRun ⟨.u k 1, z, a, b + j⟩ r := by
  induction j generalizing b with
  | zero => rfl
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, emRun, lstep]
    rw [show (ES.incTo ⟨.u k 1, z, a, b⟩ (.u k 1) (1 + 1)) = ⟨.u k 1, z, a, b + 1⟩ from rfl,
      ih]
    congr 2
    omega

/-- The emitter on the argument list of a gate (at most two arguments): it emits the
gate's clauses and moves to the next gate.

**Proof sketch.** Cases on the argument list; each unary argument is counted into its
counter (`emRun_u0`, `emRun_u1`), and the closing `0` runs the emission program, which
prints the Tseitin clauses (`emitBits_eq`). -/
private theorem emRun_args (k : GateKind) (z : ℕ) (args : List ℕ) (h : args.length ≤ 2)
    (r : List Bool) :
    emRun ⟨.l k 0, z, 0, 0⟩ (encodeList encodeNat args ++ r) =
      serBody (DAGGate.tseitin z ⟨k, args⟩) ++ emRun ⟨.g, z + 1, 0, 0⟩ r := by
  match args, h with
  | [], _ =>
    simp only [encodeList, List.cons_append, List.nil_append, emRun, lstep]
    rw [emitBits_eq]
    rfl
  | [j], _ =>
    simp only [encodeList, encodeNat, List.cons_append, List.nil_append, List.append_assoc,
      emRun, lstep]
    simp only [Fin.isValue, Fin.reduceEq, if_false]
    rw [emRun_u0]
    simp only [emRun, lstep, Nat.zero_add]
    rw [emitBits_eq]
    rfl
  | [j, l], _ =>
    simp only [encodeList, encodeNat, List.cons_append, List.nil_append, List.append_assoc,
      emRun, lstep]
    simp only [Fin.isValue, Fin.reduceEq, if_false]
    rw [emRun_u0]
    simp only [emRun, lstep, Nat.zero_add, Fin.isValue, Fin.reduceAdd, Fin.reduceEq,
      if_false]
    rw [emRun_u1]
    simp only [emRun, lstep, Nat.zero_add]
    rw [emitBits_eq]
    rfl

/-- The emitter on the gate list: it emits the clauses of every gate (vertex `z`
onwards) and then the formula terminator.

**Proof sketch.** Induction on the gate list: a gate's continue bit and label lead to the
argument phase (`hk`), the argument list emits the gate's clauses (`emRun_args`), and the
end-of-list bit emits the terminator. -/
private theorem emRun_gates (z : ℕ) (gs : List DAGGate) (h : ∀ g ∈ gs, g.args.length ≤ 2)
    (r : List Bool) :
    emRun ⟨.g, z, 0, 0⟩ (encodeList DAGGate.encode gs ++ r) =
      serBody (tseitinGates z gs) ++ [false] := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨k, args⟩ := g
    have hk : ∀ r', emRun ⟨.g, z, 0, 0⟩ (true :: (GateKind.encode k ++ r')) =
        emRun ⟨.l k 0, z, 0, 0⟩ r' := by
      intro r'
      cases k <;> rfl
    simp only [encodeList, DAGGate.encode, List.cons_append, List.append_assoc]
    rw [hk, emRun_args k z args (h ⟨k, args⟩ (by simp)),
      ih (z + 1) (fun g hg => h g (by simp [hg]))]
    simp [tseitinGates, serBody]

/-- **The emitter is correct on descriptions**: on the description of a circuit whose
gates have at most two arguments (e.g. a fan-in-two circuit), it outputs the
serialization of the Tseitin clauses of all gates, `CNF.serialize (tseitinGates n
C.gates)` — the Tseitin formula `DAGCircuit.toCNF` without its output clause.

**Proof sketch.** The leading `1ⁿ0` sets the vertex counter to `n` (`emRun_n`); then the
gate list is processed gate by gate (`emRun_gates`): each gate's label and arguments are
read and its clauses at vertex `z` emitted (`emRun_args`), and the end of the list emits
the terminator. -/
theorem gateClauses_encode {n : ℕ} (C : DAGCircuit n) (h : ∀ g ∈ C.gates, g.args.length ≤ 2) :
    gateClauses C.encode = CNF.serialize (tseitinGates n C.gates) := by
  simp only [gateClauses, DAGCircuit.encode, encodeNat, List.append_assoc]
  rw [emRun_n]
  simp only [List.singleton_append, emRun, lstep, Nat.zero_add]
  rw [emRun_gates n C.gates h, serialize_eq_serBody]

end Emitter

end CktSatReduction

end BoolCircuit
