<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.DAGCircuit.exists_isStrict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Circuit Conversion

**Claim.** For a positive number of inputs, a well-formed circuit with at most two arguments per gate has an equivalent strict circuit in which every non-output vertex has positive fanout, with size at most four times the original size plus twelve.

**Proof.** Use the circuit produced by strictification, which is available under the positive-input hypothesis. It is strict in the stated sense: its gates have distinct arguments and the required arities, and each non-output vertex has positive fanout (`BoolCircuit.DAGCircuit.strictify_isStrict`). Its evaluation agrees with the original circuit on every input (`BoolCircuit.DAGCircuit.strictify_eval`), and its size is at most four times the original size plus twelve (`BoolCircuit.DAGCircuit.strictify_size_le`). These three properties establish the result.

**Key facts.** `BoolCircuit.DAGCircuit.strictify_isStrict`, `BoolCircuit.DAGCircuit.strictify_eval`, `BoolCircuit.DAGCircuit.strictify_size_le`.
