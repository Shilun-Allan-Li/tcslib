import TCSlib.Complexity.CircuitComplexity.FormulaArith.CarrySave
set_option autoImplicit false
attribute [local irreducible] BoolCircuit.FormulaArith.val
-- pos_sealed: reads `BoolCircuit.FormulaArith.val` through its reader
example (x : Fin 2 → Bool) (U : List (BoolCircuit.TreeCircuit 2)) : BoolCircuit.FormulaArith.val x U = BoolCircuit.bitsVal (U.map fun c => c.eval x) :=
  BoolCircuit.FormulaArith.val_eq x U
