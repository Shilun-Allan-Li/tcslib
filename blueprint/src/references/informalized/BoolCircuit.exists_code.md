<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGHardFunctions.lean :: BoolCircuit.exists_code -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Code for a bounded fan-in circuit

**Claim.** Every well-formed acyclic Boolean circuit with at most two inputs per gate and size at most $S$ has a code of size parameter $S$ whose evaluation agrees with the circuit.

**Proof.** Let the code list exactly the circuit's gates, in their given topological order, and use the circuit's output vertex as the coded output. For each gate position within the circuit, encode its kind and its at most two input indices; fill all remaining code positions with a fixed default gate. The size bound ensures that the number of gates fits within the $S$ available positions and that every circuit vertex index is below $S$. Each actual gate has distinct inputs and, if it is a NOT gate, exactly one input, so decoding its encoding recovers that gate (`BoolCircuit.decodeGate_encodeGate`). Consequently the decoded list of gates is precisely the original list. The input list and output index are also unchanged, so evaluating the code gives the same result as evaluating the circuit on every assignment.

**Key facts.** `BoolCircuit.decodeGate_encodeGate`.
