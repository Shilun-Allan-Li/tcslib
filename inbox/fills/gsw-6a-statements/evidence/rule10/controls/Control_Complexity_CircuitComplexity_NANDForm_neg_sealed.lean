import TCSlib.Complexity.CircuitComplexity.NANDForm
set_option autoImplicit false
attribute [local irreducible] BoolCircuit.DAGGate.IsNAND
-- neg_sealed: reads `BoolCircuit.DAGGate.IsNAND` through its body
example (g : BoolCircuit.DAGGate) : g.IsNAND ↔ g.kind = .not ∧ g.args.length ≤ 2 :=
  Iff.rfl
