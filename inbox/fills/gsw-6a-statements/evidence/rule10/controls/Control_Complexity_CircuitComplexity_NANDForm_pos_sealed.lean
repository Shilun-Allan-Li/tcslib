import TCSlib.Complexity.CircuitComplexity.NANDForm
set_option autoImplicit false
attribute [local irreducible] BoolCircuit.DAGGate.IsNAND
-- pos_sealed: reads `BoolCircuit.DAGGate.IsNAND` through its reader
example (g : BoolCircuit.DAGGate) : g.IsNAND ↔ g.kind = .not ∧ g.args.length ≤ 2 :=
  BoolCircuit.DAGGate.isNAND_iff g
