<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.edge_c1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Integer Reconstruction

**Claim.** For every integer $e$, recovering an integer by negating the unsigned index plus one when $e$ is negative, and using the unsigned index otherwise, gives $e$.

**Proof.** Split according to whether $e<0$. In the negative case, the sign bit is true and the unsigned index is $-e-1$; adding one gives $-e$, whose negation is $e$. In the nonnegative case, the sign bit is false and the unsigned index is $e$, so the reconstruction returns $e$ directly.
