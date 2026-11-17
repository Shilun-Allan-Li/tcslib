import TCSlib.Complexity.CircuitComplexity.NANDForm
set_option autoImplicit false
-- neg_unsealed: reads `BoolCircuit.DAGGate.IsNAND` through its body
example (g : BoolCircuit.DAGGate) : g.IsNAND ↔ g.kind = .not ∧ g.args.length ≤ 2 :=
  Iff.rfl
