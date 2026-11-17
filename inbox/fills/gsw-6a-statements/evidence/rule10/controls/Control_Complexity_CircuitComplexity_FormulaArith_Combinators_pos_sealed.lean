import TCSlib.Complexity.CircuitComplexity.FormulaArith.Combinators
set_option autoImplicit false
attribute [local irreducible] BoolCircuit.TreeCircuit.balanced
-- pos_sealed: reads `BoolCircuit.TreeCircuit.balanced` through its reader
example (b : Bool) : BoolCircuit.TreeCircuit.balanced b ([] : List (BoolCircuit.TreeCircuit 2)) = .node b [] :=
  BoolCircuit.TreeCircuit.balanced_nil b
