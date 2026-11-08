<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.DAGCircuit.strictify_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation preserved by strictification

**Claim.** For positive input count, strictification preserves the circuit’s output on every Boolean input assignment, assuming the gates have distinct arguments, NOT gates have one argument, and all gates have at most two arguments.

**Proof.** Strictification first applies deconstantization and then sealing. Sealing preserves evaluation (`DAGCircuit.seal_eval`), so the output of the sealed, deconstantized circuit equals that of the deconstantized circuit. Deconstantization preserves evaluation under the stated fan-in and well-formedness assumptions (`DAGCircuit.deconst_eval`). Combining these equalities proves that strictification preserves the original output.

**Key facts.** `BoolCircuit.DAGCircuit.seal_eval`, `BoolCircuit.DAGCircuit.deconst_eval`.
