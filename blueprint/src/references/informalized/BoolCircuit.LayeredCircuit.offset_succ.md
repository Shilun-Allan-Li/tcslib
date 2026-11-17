<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.offset_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Formula for the Layer Offset

**Claim.** For every natural number $m$, the offset at $m+1$ is the offset at $m$ plus the number of nodes in layer $m+1$ when $m<\mathrm{depth}(F)$, and equals the offset at $m$ otherwise.

**Proof.** The offset is a sum over indices below its argument. Passing from $m$ to $m+1$ adds exactly the final summand, namely the successor-layer cardinality at index $m$. By definition, this cardinality is the number of nodes in layer $m+1$ when $m$ is below the depth, and zero otherwise.
