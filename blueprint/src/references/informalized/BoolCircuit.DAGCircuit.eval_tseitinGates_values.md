<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.DAGCircuit.eval_tseitinGates_values -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Values Satisfy Gate Clauses

**Claim.** For a circuit whose gates have at most two arguments, assigning each vertex its value from evaluation makes the conjunction of all its Tseitin gate clauses true.

**Proof.** The conjunction of all Tseitin gate clauses is true exactly when each gate's individual Tseitin encoding is true (`BoolCircuit.eval_tseitinGates`). Consider a gate at position $i$, whose output vertex is $n+i$. Its encoding is true precisely when the assigned value at that vertex equals the gate's evaluation on the preceding values (`BoolCircuit.DAGGate.eval_tseitin`). The assignment under consideration uses the circuit's computed values, and the value at vertex $n+i$ is exactly the evaluation of gate $i$ on the circuit value list (`BoolCircuit.DAGCircuit.values_getD_gate`). Thus every gate encoding is true, so their conjunction is true.

**Key facts.** `BoolCircuit.eval_tseitinGates`, `BoolCircuit.DAGGate.eval_tseitin`, `BoolCircuit.DAGCircuit.values_getD_gate`.
