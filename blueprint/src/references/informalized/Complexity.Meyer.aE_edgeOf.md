<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerComplete.lean :: Complexity.Meyer.aE_edgeOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding Signed Boundary Positions

**Claim.** For either Boolean choice of sign and every natural number $a$, encoding the corresponding signed boundary position with $a(e)$ recovers $a$.

**Proof.** Consider the two Boolean cases. When the sign is true, the boundary position is $e=-a-1$, which is negative; applying the negative branch of $a(e)$ gives $-(-a-1)-1=a$. When the sign is false, $e=a$ is nonnegative, and the other branch gives $a(e)=e=a$.
