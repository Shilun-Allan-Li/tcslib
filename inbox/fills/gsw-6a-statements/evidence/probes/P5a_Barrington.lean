import TCSlib.Complexity.BranchingPrograms.Barrington

/-! Probe P5a (Theorem 1, `barrington`; part a of P5, split to keep each Lean run short).  `barrington` is defined by well-founded recursion, so
the kernel does not reduce it; the checks are `#eval` (compiled evaluation), recorded as evidence,
never as proofs.  For each test formula `c` (two inputs) and EACH of the 24 five-cycles `σ`:
* recognition with output `σ` (C13): `∀ x, yield x = if c.eval x then σ else id`;
* `barrington_yield_zero`'s reading (C16): `∀ x, yield x 0 = if c.eval x then σ 0 else 0`;
* length `≤ 4 ^ depth` (C14) and `0 < length`;
* permutation program (C15): every map of every instruction is a bijection.
Formulas: `x₀ ∧ x₁`, `x₀ ∨ ¬x₁`, both constants, a fan-in-1 node, and two depth-2 formulas
(XOR as an `∧` of `∨`s and as an `∨` of `∧`s), plus a depth-4 one with a nested constant. -/

open BranchingProgram BoolCircuit Equiv

namespace P5a

def fiveCycles : List (Perm (Fin 5)) :=
  [List.formPerm [0, 1, 2, 3, 4],
    List.formPerm [0, 1, 2, 4, 3],
    List.formPerm [0, 1, 3, 2, 4],
    List.formPerm [0, 1, 3, 4, 2],
    List.formPerm [0, 1, 4, 2, 3],
    List.formPerm [0, 1, 4, 3, 2],
    List.formPerm [0, 2, 1, 3, 4],
    List.formPerm [0, 2, 1, 4, 3],
    List.formPerm [0, 2, 3, 1, 4],
    List.formPerm [0, 2, 3, 4, 1],
    List.formPerm [0, 2, 4, 1, 3],
    List.formPerm [0, 2, 4, 3, 1],
    List.formPerm [0, 3, 1, 2, 4],
    List.formPerm [0, 3, 1, 4, 2],
    List.formPerm [0, 3, 2, 1, 4],
    List.formPerm [0, 3, 2, 4, 1],
    List.formPerm [0, 3, 4, 1, 2],
    List.formPerm [0, 3, 4, 2, 1],
    List.formPerm [0, 4, 1, 2, 3],
    List.formPerm [0, 4, 1, 3, 2],
    List.formPerm [0, 4, 2, 1, 3],
    List.formPerm [0, 4, 2, 3, 1],
    List.formPerm [0, 4, 3, 1, 2],
    List.formPerm [0, 4, 3, 2, 1]]

def x0 : TreeCircuit 2 := .lit ⟨0, true⟩
def x1 : TreeCircuit 2 := .lit ⟨1, true⟩
def nx0 : TreeCircuit 2 := .lit ⟨0, false⟩
def nx1 : TreeCircuit 2 := .lit ⟨1, false⟩

def tests : List (String × TreeCircuit 2) :=
  [("x0 ∧ x1", .node true [x0, x1]),
   ("x0 ∨ ¬x1", .node false [x0, nx1]),
   ("true", .node true []),
   ("false", .node false []),
   ("fan-in 1: ∨[¬x1]", .node false [nx1])]

def recognizes (c : TreeCircuit 2) (σ : Perm (Fin 5)) : Bool :=
  decide (∀ x : Fin 2 → Bool, (barrington c σ).yield x = if c.eval x then ⇑σ else id)

def readsZero (c : TreeCircuit 2) (σ : Perm (Fin 5)) : Bool :=
  decide (∀ x : Fin 2 → Bool, (barrington c σ).yield x 0 = if c.eval x then σ 0 else 0)

def lengthOk (c : TreeCircuit 2) (σ : Perm (Fin 5)) : Bool :=
  decide ((barrington c σ).length ≤ 4 ^ c.depth) && decide (0 < (barrington c σ).length)

def isPerm (c : TreeCircuit 2) (σ : Perm (Fin 5)) : Bool :=
  (barrington c σ).instrs.all fun ι =>
    decide (Function.Bijective ι.map0) && decide (Function.Bijective ι.map1)

-- per formula: name, depth, maxFanin, length at sigma1, and the four checks over all 24 σ
#eval tests.map fun (s, c) =>
  (s, c.depth, c.maxFanin, (barrington c sigma1).length,
    fiveCycles.all (recognizes c), fiveCycles.all (readsZero c),
    fiveCycles.all (lengthOk c), fiveCycles.all (isPerm c))

-- the overall verdict
#eval tests.all fun (_, c) => fiveCycles.all fun σ =>
  recognizes c σ && readsZero c σ && lengthOk c σ && isPerm c σ

-- a non-five-cycle output breaks recognition of the AND (C13 needs `IsFiveCycle σ`)
#eval recognizes (.node true [x0, x1]) (Equiv.swap 0 1)

end P5a
