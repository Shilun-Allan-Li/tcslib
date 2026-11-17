<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.DAGCircuitFamily.strictify_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation preserved by strictification

**Claim.** For a family whose circuits are well formed and have fan-in at most two, strictification preserves the output of every circuit on every input.

**Proof.** Proceed by cases on the input length. At length zero, the strictified circuit and the original circuit coincide, so their evaluations are equal. At length $n+1$, apply the circuit-level preservation result to the circuit at that length. The family hypothesis supplies the required well-formedness and fan-in bound, and that result gives equality of the two evaluations on the given input.

**Key facts.** `BoolCircuit.DAGCircuit.strictify_eval`.
