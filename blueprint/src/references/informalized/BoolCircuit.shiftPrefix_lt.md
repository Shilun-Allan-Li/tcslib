<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.shiftPrefix_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix shift upper bound

**Claim.** If $v<n+i$, then the prefix shift $f_n(v)$ is less than $n+3+i$.

**Proof.** Split according to whether $v<n$. If so, $f_n(v)=v$, and the assumed bound gives $v<n+i<n+3+i$. Otherwise $f_n(v)=v+3$; combining $v<n+i$ with this formula gives $v+3<n+i+3=n+3+i$.
