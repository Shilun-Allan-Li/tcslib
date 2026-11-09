/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.Uniform
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The circuit-value algorithm: a streaming automaton and its semantics

[AB09] uses repeatedly that "evaluating a circuit on an input can be done in polynomial
time" (proofs of Thm 6.13, Thm 6.18, Thm 6.19, and "CKT-SAT is clearly in NP", p. 111).
This file is the machine-independent half of that fact for the book-model circuits
`BoolCircuit.DAGCircuit` and their description `BoolCircuit.DAGCircuit.encode`: a
one-pass streaming algorithm over the description, with a growing list of vertex values,
and the proof that it accepts exactly the descriptions of fan-in-two circuits that
output `1`. `TCSlib.Complexity.CircuitComplexity.CircuitEval` implements it as a
two-work-tape Turing machine.

The algorithm reads the description bit by bit, in a finite-control *phase*
(`BoolCircuit.CircuitEval.Ph`). It skips the number of inputs, then for each gate reads
its label and its arguments: for an argument `a` (in unary) it walks the value list to
cell `a`, reads the value, folds it into an accumulator held in the control, and marks
cell `a` on a second list (a repeated argument finds its mark and is rejected). At the
end of the argument list it appends the gate's value to the value list. Finally it walks
to the output vertex and outputs its value. Every syntax error, out-of-range vertex, third
argument, repeated argument or `¬` gate with other than one argument rejects at once.

The single-bit actions are a finite table, `BoolCircuit.CircuitEval.lact`, shared with
the Turing machine; the abstract run `BoolCircuit.CircuitEval.absRun` is *defined* from
it, so that the machine simulates the abstract run step by step.

## Main definitions

* `BoolCircuit.CircuitEval.lact` — the action of the algorithm on one description bit.
* `BoolCircuit.CircuitEval.absRun` — the algorithm's verdict from a given state.
* `BoolCircuit.CircuitEval.verdict` — the verdict on a paired string
  `Turing.pairEncode code x`: read the number of inputs `n`, check `n ≤ |x|` (and
  `n = |x|` if `exact`), and run the algorithm on the first `n` bits of `x`.

## Main results

This file only defines the algorithm; its correctness
(`BoolCircuit.CircuitEval.verdict_pairEncode`) is proved in
`TCSlib.Complexity.CircuitComplexity.CircuitEvalCorrect`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.1–§6.2; p. 111, Theorems 6.13, 6.18, 6.19.)
-/

namespace BoolCircuit

namespace CircuitEval

/-! ## The algorithm's finite control -/

/-- The phases of the algorithm, each expecting the next description bit: reading the
number of inputs during setup (`n0`) and scanning to the end of the description (`sep`);
then, in the main pass, skipping the number of inputs (`skipN`), expecting a gate or the
end of the gate list (`g`), reading the two label bits (`k1`, `k2`), reading an argument
list (`a`: label, number of arguments so far, accumulator), walking a unary argument
(`u`), walking the output vertex (`o`), and expecting the end of the description with
the output value in hand (`fin`). -/
inductive Ph
  | n0
  | sep
  | skipN
  | g
  | k1
  | k2 (b : Bool)
  | a (k : GateKind) (c : Fin 3) (acc : Bool)
  | u (k : GateKind) (c : Fin 3) (acc : Bool)
  | o
  | fin (v : Bool)
  deriving DecidableEq, Fintype

/-- The control states of the Turing machine implementing the algorithm: the two halves
of reading a doubled description bit (`rd1`, `rd2`), rewinding the mark tape (`rewM`),
copying the input to the value tape (`copy`), rewinding the value tape (`rewV`, then
either the input rewind or a phase), rewinding the input (`rewI0`, `rewI`), and
appending a gate value (`app`). -/
inductive St
  | rd1 (φ : Ph)
  | rd2 (φ : Ph) (b : Bool)
  | rewM
  | copy
  | rewV (d : Option Ph)
  | rewI0
  | rewI
  | app (v : Bool)
  deriving DecidableEq, Fintype

/-- The label read from two label bits (`GateKind.encode`); `11` is rejected before
this is used. -/
def kindOf : Bool → Bool → GateKind
  | false, false => .and
  | false, true => .or
  | _, _ => .not

/-- The accumulator's initial value: the empty `∨` is `false`, the empty `∧` is
`true`. -/
def accInit : GateKind → Bool
  | .or => false
  | _ => true

/-- Fold one argument value into the accumulator. -/
def accComb : GateKind → Bool → Bool → Bool
  | .or, acc, v => acc || v
  | _, acc, v => acc && v

/-- The gate value from the final accumulator (a `¬` gate negates). -/
def accFin : GateKind → Bool → Bool
  | .not, acc => !acc
  | _, acc => acc

/-- A logical action: optional writes on the value tape and the mark tape, the common
head move, an optional output symbol, and the next state (`none` halts). -/
structure LA where
  /-- write on the value tape -/
  vw : Option (Option Bool)
  /-- write on the mark tape -/
  mw : Option (Option Bool)
  /-- the move of both work heads -/
  hm : SignType
  /-- the emitted symbol -/
  o : Option Bool
  /-- the next state -/
  q : Option St

/-- Reject: output `0` and halt. -/
def LA.rej : LA := ⟨none, none, 0, some false, none⟩

/-- Go to a state without touching the tapes. -/
def LA.go (q : St) : LA := ⟨none, none, 0, none, some q⟩

/-- **The algorithm on one description bit.** Given the phase, the bit (`none` for the
end of the description), and the cells under the value-tape and mark-tape heads,
return the action. Everything not listed rejects. -/
def lact : Ph → Option Bool → Option Bool → Option Bool → LA
  | .n0, some true, _, _ => ⟨none, some (some true), .pos, none, some (.rd1 .n0)⟩
  | .n0, some false, _, _ => .go (.rd1 .sep)
  | .sep, some _, _, _ => .go (.rd1 .sep)
  | .sep, none, _, _ => ⟨none, none, .neg, none, some .rewM⟩
  | .skipN, some true, _, _ => .go (.rd1 .skipN)
  | .skipN, some false, _, _ => .go (.rd1 .g)
  | .g, some true, _, _ => .go (.rd1 .k1)
  | .g, some false, _, _ => .go (.rd1 .o)
  | .k1, some b, _, _ => .go (.rd1 (.k2 b))
  | .k2 b₁, some b₂, _, _ =>
    if b₁ && b₂ then .rej else .go (.rd1 (.a (kindOf b₁ b₂) 0 (accInit (kindOf b₁ b₂))))
  | .a k c acc, some true, _, _ => if c = 2 then .rej else .go (.rd1 (.u k c acc))
  | .a k c acc, some false, _, _ =>
    if k = .not ∧ c ≠ 1 then .rej else .go (.app (accFin k acc))
  | .u k c acc, some true, some _, _ => ⟨none, none, .pos, none, some (.rd1 (.u k c acc))⟩
  | .u k c acc, some false, some v, none =>
    ⟨none, some (some true), .neg, none, some (.rewV (some (.a k (c + 1) (accComb k acc v))))⟩
  | .o, some true, some _, _ => ⟨none, none, .pos, none, some (.rd1 .o)⟩
  | .o, some false, some v, _ => .go (.rd1 (.fin v))
  | .fin v, none, _, _ => ⟨none, none, 0, some v, none⟩
  | _, _, _, _ => .rej

/-! ## The abstract run -/

/-- The abstract state of the main pass: the phase, the value list, the marked cells,
and the position of the work heads. -/
structure AS where
  /-- the phase -/
  φ : Ph
  /-- the vertex values computed so far -/
  vals : List Bool
  /-- the marked cells of the mark tape -/
  ms : List ℕ
  /-- the work-head position -/
  j : ℕ

/-- The mark-tape cell at `j`. -/
def markCell (ms : List ℕ) (j : ℕ) : Option Bool := if j ∈ ms then some true else none

/-- The abstract effect of a logical action from state `s`: halt with the emitted bit,
continue in a reading phase, or (after the machine's rewind or append excursion)
continue at head position `0`. -/
def absOf (s : AS) (la : LA) : AS ⊕ Bool :=
  match la.q with
  | none => .inr (la.o.getD false)
  | some (.rd1 φ') =>
    .inl ⟨φ', s.vals, if la.mw = some (some true) then s.j :: s.ms else s.ms,
      if la.hm = .pos then s.j + 1 else s.j⟩
  | some (.rewV (some φ')) =>
    .inl ⟨φ', s.vals, if la.mw = some (some true) then s.j :: s.ms else s.ms, 0⟩
  | some (.app v) => .inl ⟨.g, s.vals ++ [v], [], 0⟩
  | some _ => .inr false

/-- One abstract step on a description bit (`none`: end of the description). -/
def absStep (s : AS) (sym : Option Bool) : AS ⊕ Bool :=
  absOf s (lact s.φ sym s.vals[s.j]? (markCell s.ms s.j))

/-- **The algorithm's verdict** from state `s` on the remaining description bits. -/
def absRun : AS → List Bool → Bool
  | s, [] => match absStep s none with
    | .inl _ => false
    | .inr v => v
  | s, b :: l => match absStep s (some b) with
    | .inl s' => absRun s' l
    | .inr v => v

/-- The number of leading `1`s of a string: the number of inputs of a description. -/
def leadOnes (code : List Bool) : ℕ := (code.takeWhile (· == true)).length

/-- **The verdict on a paired string** `pairEncode code x`: the number of inputs `n` is
the leading unary number of `code` (which must be terminated); require `n ≤ |x|`, and
`n = |x|` when `exact`; then run the algorithm on the first `n` bits of `x`. A string
that is not a pair is rejected. -/
def verdict (exact : Bool) (z : List Bool) : Bool :=
  match Turing.pairDecode z with
  | none => false
  | some (code, x) =>
    if false ∈ code ∧ leadOnes code ≤ x.length ∧
        (exact = false ∨ leadOnes code = x.length)
    then absRun ⟨.skipN, x.take (leadOnes code), [], 0⟩ code
    else false

end CircuitEval

end BoolCircuit
