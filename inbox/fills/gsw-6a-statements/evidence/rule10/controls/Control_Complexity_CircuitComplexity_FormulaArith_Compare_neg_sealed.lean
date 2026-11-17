import TCSlib.Complexity.CircuitComplexity.FormulaArith.Compare
set_option autoImplicit false
attribute [local irreducible] BoolCircuit.FormulaArith.bitAt
-- neg_sealed: reads `BoolCircuit.FormulaArith.bitAt` through its body
example (x : Fin 2 → Bool) (U : List (BoolCircuit.TreeCircuit 2)) (j : ℕ) : BoolCircuit.FormulaArith.bitAt x U j = (U.map fun c => c.eval x).getD j false :=
  rfl
