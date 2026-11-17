import TCSlib.Complexity.CircuitComplexity.FormulaArith.Combinators
set_option autoImplicit false
-- neg_unsealed: reads `BoolCircuit.TreeCircuit.balanced` through its body
example (b : Bool) : BoolCircuit.TreeCircuit.balanced b ([] : List (BoolCircuit.TreeCircuit 2)) = .node b [] :=
  rfl
