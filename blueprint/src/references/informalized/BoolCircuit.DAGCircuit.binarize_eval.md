<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.DAGCircuit.binarize_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the binarized circuit

**Claim.** For every input assignment, binarizing a directed acyclic circuit with distinct gate arguments and unary negation gates preserves its output.

**Proof.** The general evaluation-preservation theorem for circuit rewriting states that replacing each gate by a gadget that computes the same gate function preserves the circuit's output on every input (`DAGCircuit.rewrite_eval`). The binarization gadget is correct for gates satisfying the given hypotheses, and the well-formedness assumption supplies those hypotheses for every gate. Apply the rewrite theorem to this gadget and the input assignment $x$ to obtain equality of the two circuit evaluations.

**Key facts.** `BoolCircuit.DAGCircuit.rewrite_eval`.
