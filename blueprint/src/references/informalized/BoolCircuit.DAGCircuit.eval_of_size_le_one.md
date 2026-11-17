<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPoly.lean :: BoolCircuit.DAGCircuit.eval_of_size_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a One-Input Circuit

**Claim.** A directed acyclic Boolean circuit with one input and size at most $1$ outputs that input on every assignment.

**Proof.** Since the size is the number of inputs plus the number of gates, the size bound $1$ with one input forces the circuit to have no gates. The output-vertex condition then forces its output index to be $0$. With no gates, the value at that vertex is the original input value, so the circuit outputs $x(0)$ (`BoolCircuit.DAGCircuit.values_getD_input`).

**Key facts.** `BoolCircuit.DAGCircuit.values_getD_input`.
