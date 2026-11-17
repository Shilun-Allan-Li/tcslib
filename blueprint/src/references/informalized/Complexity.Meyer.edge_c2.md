<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.edge_c2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Reconstruction

**Claim.** For every integer $e$, recovering an integer by negating the unsigned index when $e$ is negative, and using the unsigned index plus one otherwise, gives $e+1$.

**Proof.** Split according to whether $e<0$. In the negative case, the sign bit is true and the unsigned index is $-e-1$; negating it gives $e+1$. In the nonnegative case, the sign bit is false and the unsigned index is $e$, so adding one gives $e+1$.
