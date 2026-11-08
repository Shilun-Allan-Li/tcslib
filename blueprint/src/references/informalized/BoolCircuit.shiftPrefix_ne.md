<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictCircuit.lean :: BoolCircuit.shiftPrefix_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Avoiding the shifted prefix

**Claim.** For $k<3$, the prefix shift $f_n(v)$ is not equal to $n+k$.

**Proof.** Split according to whether $v<n$. In the first case $f_n(v)=v<n$, whereas $n+k\ge n$, so equality is impossible. In the second case $f_n(v)=v+3\ge n+3$, while $k<3$ gives $n+k<n+3$. Thus equality is again impossible.
