<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Cube.lean :: BooleanAnalysis.GaussianSpace.derivative_restrictLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a Coordinate Restriction

**Claim.** The discrete derivative in direction $i$ of the restriction of $f$ to last coordinate $b$, evaluated at $x$, equals the derivative of $f$ in coordinate $i$ at the point obtained by appending $b$ to $x$.

**Proof.** Expanding both derivatives, each is one half of the difference between the values of $f$ at the points obtained by setting coordinate $i$ first to false and then to true, while keeping the last coordinate equal to $b$. Updating coordinate $i$ before or after appending the last coordinate gives the same point, so the two differences agree.
