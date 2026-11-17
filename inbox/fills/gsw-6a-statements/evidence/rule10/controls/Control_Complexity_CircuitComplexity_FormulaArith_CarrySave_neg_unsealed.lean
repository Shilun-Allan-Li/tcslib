import TCSlib.Complexity.CircuitComplexity.FormulaArith.CarrySave
set_option autoImplicit false
-- neg_unsealed: reads `BoolCircuit.FormulaArith.val` through its body
example (x : Fin 2 → Bool) (U : List (BoolCircuit.TreeCircuit 2)) : BoolCircuit.FormulaArith.val x U = BoolCircuit.bitsVal (U.map fun c => c.eval x) :=
  rfl
