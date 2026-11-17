import TCSlib.Complexity.CircuitComplexity.FormulaArith.Compare
set_option autoImplicit false
attribute [local irreducible] BoolCircuit.FormulaArith.bitAt
-- pos_sealed: reads `BoolCircuit.FormulaArith.bitAt` through its reader
example (x : Fin 2 → Bool) (U : List (BoolCircuit.TreeCircuit 2)) (j : ℕ) : BoolCircuit.FormulaArith.bitAt x U j = (U.map fun c => c.eval x).getD j false :=
  BoolCircuit.FormulaArith.bitAt_eq x U j
