<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGHardFunctions.lean :: BoolCircuit.decodeKind_encodeKind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering an encoded gate kind

**Claim.** For each of the three gate kinds—AND, OR, and NOT—decoding its encoding returns that same kind.

**Proof.** Check the three possibilities for the gate kind. In each case, the encoding is the corresponding one of the three distinguished indices, and the decoder maps that index back to the same constructor.
