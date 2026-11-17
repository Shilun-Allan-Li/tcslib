<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon.lean :: BoolCircuit.DAGCircuit.size_canon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size preserved by canonicalization

**Claim.** Canonicalization preserves the size of a finite Boolean circuit.

**Proof.** Unfolding the definitions of size and canonicalization shows that canonicalization leaves the number of gates, and hence the input count plus gate count, unchanged. Therefore the two sizes are equal.
