<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.DAGCircuit.seal_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Preserved by Sealing

**Claim.** For every Boolean input assignment, sealing the circuit preserves its output value.

**Proof.** The sealing specification (`seal_spec`) states that the sealed gates and designated output satisfy the specification's value clause. Apply that clause to the given input assignment: the output of the sealed circuit equals the original circuit's output.

**Key facts.** `BoolCircuit.seal_spec`.
