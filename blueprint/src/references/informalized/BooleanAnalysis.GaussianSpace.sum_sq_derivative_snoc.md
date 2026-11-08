<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Cube.lean :: BooleanAnalysis.GaussianSpace.sum_sq_derivative_snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Derivatives Under Restriction

**Claim.** For a Boolean function on the $n+1$ dimensional cube, the sum of squared coordinate half-differences at $(x,b)$ is the corresponding sum for the restriction fixing the last coordinate to $b$, plus the square of the last-coordinate half-difference.

**Proof.** Split the sum over the $n+1$ coordinates into the first $n$ coordinates and the last one. For each of the first $n$ coordinates, the derivative of the restriction fixing the last coordinate to $b$ equals the corresponding derivative of the original function at $(x,b)$ (`derivative_restrictLast`). The derivative in the last coordinate at $(x,b)$ is the last-coordinate difference itself (`derivative_last_snoc`). Substituting these identities into the split sum gives the stated equality.

**Key facts.** `BooleanAnalysis.GaussianSpace.derivative_restrictLast`, `BooleanAnalysis.GaussianSpace.derivative_last_snoc`.
