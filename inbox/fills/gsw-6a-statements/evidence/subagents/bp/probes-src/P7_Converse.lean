import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.Perm.Basic
import TCSlib.Complexity.BranchingPrograms.BarringtonConverse

/-! Probe P7 (Theorem 2).  `compTree` is defined by well-founded recursion (not
kernel-reducible) and `toFormula` is `noncomputable` (it enumerates the `Finset` by
`Finset.toList`), so the checks are `#eval`, recorded as evidence.  `toFormula` is checked
through `topFormula`, a probe-local computable copy of its body taking the accepting set as an
explicit list `Fl` in place of `F.toList` (same expression otherwise; `toFormula_eq`).
* On P1's XOR program (width 2, eight inputs): every wire `compTree B.instrs i j` agrees with
  `decide (B.yield x i = j)` on all 256 inputs (C19); the acceptance formula agrees with
  `decide (B.yield x ∈ F)` for every accepting set `F ⊆ {id, swap}` (C20); depths against C19's
  bound `(⌈log₂ w⌉ + 2)·⌈log₂ l⌉ + 1` and C21's bound `… + topDepth w`; fan-in `≤ 2`.
* The (fix) constants on a sweep: programs of every length `l ≤ 17` and width `w ≤ 4`, depth of
  every wire against C19's bound, and `topFormula` with the largest accepting set (all `w^w`
  maps) against C21's bound; the maximum slack is printed. -/

open BranchingProgram BoolCircuit Equiv

namespace P7

def t : Perm (Fin 2) := Equiv.swap 0 1

def xorEx : BranchingProgram 2 8 :=
  ⟨[Instr.ofPerm 6 1 t, Instr.ofPerm 3 t 1, Instr.ofPerm 7 1 t]⟩

/-- Probe-local computable copy of `toFormula` with the accepting set as a list. -/
def topFormula {w n : ℕ} (B : BranchingProgram w n) (Fl : List (Fin w → Fin w)) :
    TreeCircuit n :=
  TreeCircuit.balanced false (Fl.map fun f =>
    TreeCircuit.balanced true ((List.finRange w).map fun i => compTree B.instrs i (f i)))

-- C19 semantics on all inputs and all wires
#eval decide (∀ x : Fin 8 → Bool, ∀ i j : Fin 2,
  (compTree xorEx.instrs i j).eval x = decide (xorEx.yield x i = j))

def accSets : List (List (Fin 2 → Fin 2)) := [[], [id], [⇑t], [id, ⇑t]]

-- C20 semantics on all inputs and all accepting sets
#eval accSets.all fun Fl => decide (∀ x : Fin 8 → Bool,
  (topFormula xorEx Fl).eval x = decide (xorEx.yield x ∈ Fl))

-- depths: (max wire depth, C19 bound), (max formula depth, C21 bound), max fan-ins
#eval ((List.finRange 2).flatMap fun i => (List.finRange 2).map fun j =>
    (compTree xorEx.instrs i j).depth,
  (Nat.clog 2 2 + 2) * Nat.clog 2 xorEx.length + 1)
#eval (accSets.map fun Fl => (topFormula xorEx Fl).depth,
  (Nat.clog 2 2 + 2) * Nat.clog 2 xorEx.length + topDepth 2)
#eval ((List.finRange 2).all fun i => (List.finRange 2).all fun j =>
    decide ((compTree xorEx.instrs i j).maxFanin ≤ 2)) &&
  accSets.all fun Fl => decide ((topFormula xorEx Fl).maxFanin ≤ 2)

/-! Sweep of the depth constants. -/

/-- A deterministic instruction of width `w` on one input (the maps do not matter for depth,
but vary them anyway). -/
def mkInstr (w : ℕ) [NeZero w] (k : ℕ) : Instr w 1 :=
  ⟨0, fun i => ⟨(i.val + k) % w, Nat.mod_lt _ (Nat.pos_of_neZero w)⟩,
    fun i => ⟨(i.val * (k + 1)) % w, Nat.mod_lt _ (Nat.pos_of_neZero w)⟩⟩

def mkProg (w : ℕ) [NeZero w] (l : ℕ) : BranchingProgram w 1 :=
  ⟨(List.range l).map (mkInstr w)⟩

/-- All length-`k` tuples of elements of `Fin w`. -/
def tuples (w : ℕ) : ℕ → List (List (Fin w))
  | 0 => [[]]
  | k + 1 => (tuples w k).flatMap fun l => (List.finRange w).map (· :: l)

/-- All maps `Fin w → Fin w`, as a list (`w^w` of them). -/
def allMaps (w : ℕ) : List (Fin w → Fin w) :=
  (tuples w w).map fun l i => l.getD i i

def wireSlack (w : ℕ) [NeZero w] (l : ℕ) : ℤ :=
  let B := mkProg w l
  let d := ((List.finRange w).flatMap fun i => (List.finRange w).map fun j =>
    (compTree B.instrs i j).depth).foldr max 0
  ((Nat.clog 2 w + 2) * Nat.clog 2 B.length + 1 : ℕ) - (d : ℤ)

def topSlack (w : ℕ) [NeZero w] (l : ℕ) : ℤ :=
  let B := mkProg w l
  ((Nat.clog 2 w + 2) * Nat.clog 2 B.length + topDepth w : ℕ) -
    ((topFormula B (allMaps w)).depth : ℤ)

#eval (allMaps 3).length
-- minimum slack over the sweep (a negative value would refute the constant)
#eval ((List.range 18).map fun l => (wireSlack 1 l, wireSlack 2 l, wireSlack 3 l, wireSlack 4 l))
#eval ((List.range 10).map fun l => (topSlack 1 l, topSlack 2 l, topSlack 3 l))
#eval ((List.range 4).map fun l => topSlack 4 l)

end P7
