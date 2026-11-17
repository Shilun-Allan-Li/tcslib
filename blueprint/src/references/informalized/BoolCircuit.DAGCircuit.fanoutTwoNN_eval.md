<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.DAGCircuit.fanoutTwoNN_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation preserved by fanout reduction

**Claim.** For every input assignment, the fanout-reduced circuit computes the same value as the original strict circuit.

**Proof.** The invariant for the fanout reduction construction states that each original vertex's value is preserved at its corresponding tap vertex. Apply this to the original output vertex, which is a valid vertex of the circuit. The converted circuit designates that tap as its output, so the invariant gives equality of the two circuit evaluations.

**Key facts.** `BoolCircuit.nnGates_inv`.
