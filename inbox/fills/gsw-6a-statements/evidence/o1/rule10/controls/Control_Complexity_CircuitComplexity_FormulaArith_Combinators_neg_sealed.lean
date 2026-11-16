import TCSlib.Complexity.CircuitComplexity.FormulaArith.Combinators
set_option autoImplicit false
attribute [local irreducible] BoolCircuit.TreeCircuit.balanced
-- neg_sealed: reads `BoolCircuit.TreeCircuit.balanced` through its body
example (b : Bool) : BoolCircuit.TreeCircuit.balanced b ([] : List (BoolCircuit.TreeCircuit 2)) = .node b [] :=
  rfl
