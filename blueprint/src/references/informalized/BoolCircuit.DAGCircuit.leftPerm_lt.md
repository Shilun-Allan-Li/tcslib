<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardWire.lean :: BoolCircuit.DAGCircuit.leftPerm_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Permuted Indices

**Claim.** If $v<m+n+k$, then the interval permutation sends $v$ to a number less than $n+m+k$.

**Proof.** Split according to the three regions in the definition of the permutation. If $v<m$, its image is $n+v$, which is less than $n+m$ and hence less than $n+m+k$. If $m\le v<m+n$, its image is $v-m<n$, so it too is less than $n+m+k$. Finally, if $v\ge m+n$, the map fixes $v$, and the assumed bound gives $v<m+n+k=n+m+k$.
