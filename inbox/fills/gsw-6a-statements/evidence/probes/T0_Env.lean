import TCSlib.Complexity.CircuitComplexity.FormulaArith.Combinators

open BoolCircuit

#check (fun (n : ℕ) (f : Fin n → ℕ) => Finset.univ.sup f)

example : Nat.clog 2 10 = 4 := by decide +kernel
example : Nat.log2 10 = 3 := by decide
example : Nat.testBit 10 3 = true := by decide
example : (TreeCircuit.node true [TreeCircuit.lit ⟨(0 : Fin 2), true⟩,
    TreeCircuit.lit ⟨1, false⟩]).eval (fun i => i == 0) = true := by decide +kernel
example : (TreeCircuit.node true [TreeCircuit.lit ⟨(0 : Fin 2), true⟩,
    TreeCircuit.lit ⟨1, false⟩]).depth = 1 := by decide +kernel
example : ∀ x : Fin 3 → Bool, (TreeCircuit.node true [TreeCircuit.lit ⟨(0 : Fin 3), true⟩,
    TreeCircuit.lit ⟨1, false⟩]).eval x = (x 0 && !x 1) := by decide +kernel
mutual
def negT {n : ℕ} : TreeCircuit n → TreeCircuit n
  | .lit l => .lit ⟨l.idx, !l.sign⟩
  | .node b cs => .node (!b) (negL cs)
def negL {n : ℕ} : List (TreeCircuit n) → List (TreeCircuit n)
  | [] => []
  | c :: cs => negT c :: negL cs
end
#print negT
example {n : ℕ} (b : Bool) (cs : List (TreeCircuit n)) : negT (.node b cs) = .node (!b) (negL cs) := rfl
