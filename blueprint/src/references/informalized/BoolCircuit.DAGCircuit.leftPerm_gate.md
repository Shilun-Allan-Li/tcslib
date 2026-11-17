<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.leftPerm_gate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation on Gate Indices

**Claim.** The interval permutation that moves the first block of $m$ indices to the end sends $m+n+i$ to $n+m+i$.

**Proof.** The index $m+n+i$ is at least $m+n$, so it is in the region that the permutation fixes. Its image is therefore $m+n+i$, which equals $n+m+i$ by commutativity of addition.
