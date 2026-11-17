<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.DAGCircuit.strictify_isStrict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strictness after strictification

**Claim.** For positive input count, if a circuit has distinct gate arguments, each NOT gate has one argument, and every gate has at most two arguments, then its strictification has distinct arguments and the required exact arities, and every nonoutput vertex is read by some gate.

**Proof.** Deconstantization turns each gate into a strict gate under the given assumptions (`DAGCircuit.deconst_strict`). Apply the sealing strictness result (`DAGCircuit.seal_isStrict`) to that deconstantized circuit. Since strictification is precisely its sealing, the resulting circuit has strict gates and every in-range nonoutput vertex is read.

**Key facts.** `BoolCircuit.DAGCircuit.deconst_strict`, `BoolCircuit.DAGCircuit.seal_isStrict`.
