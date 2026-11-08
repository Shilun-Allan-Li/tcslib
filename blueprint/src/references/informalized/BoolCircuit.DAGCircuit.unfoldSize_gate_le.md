<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.DAGCircuit.unfoldSize_gate_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unfolded Size at a Gate

**Claim.** For a gate with at most two distinct inputs, the unfolded size at its vertex is at most three plus the sum of unfolded sizes at its gate-input vertices.

**Proof.** Fix gate $g$ at index $k$. Its arguments are distinct, its NOT gate (if it is one) has exactly one argument, and it has at most two arguments. The unfolding at vertex $n+k$ unfolds this gate, with each argument recursively unfolded. The size bound for unfolding a well-formed gate says its size is at most one plus the sum of the sizes of those argument trees (`BoolCircuit.size_unfoldGate_le`); polarity does not affect these sizes (`BoolCircuit.size_unfoldVertex_polarity`). By fuel independence (`BoolCircuit.DAGCircuit.unfoldVertex_fuel_congr`), each argument tree at the available recursive fuel has the same size as its unfolded size. Split the argument sum into input vertices and gate vertices. Each input vertex contributes size $1$ (`BoolCircuit.DAGCircuit.unfoldSize_input`), and there are at most two such arguments. Thus their total contribution is at most $2$. The remaining contribution is precisely the sum over gate-input vertices, giving the claimed upper bound of three plus that sum.

**Key facts.** `BoolCircuit.size_unfoldGate_le`, `BoolCircuit.size_unfoldVertex_polarity`, `BoolCircuit.DAGCircuit.unfoldVertex_fuel_congr`, `BoolCircuit.DAGCircuit.unfoldSize_input`.
