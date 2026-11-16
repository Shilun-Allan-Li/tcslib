import TCSlib.Complexity.CircuitComplexity.DAGCircuit

open BoolCircuit

example {n : ℕ} (C : DAGCircuit n) :
    C.IsFaninTwo ↔
      (∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)) ∧
        ∀ g ∈ C.gates, g.args.length ≤ 2  := Iff.rfl
