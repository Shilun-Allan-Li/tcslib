<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean :: Complexity.PathHard.four_le_nV -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound on the Vertex Count

**Claim.** For all natural numbers $K,c_0,m$, the number $2^{K(c_0+1)\ell(m)+(K+2)}$ is at least $4$.

**Proof.** The exponent is at least $2$, since its first summand is nonnegative and $K+2\ge2$. Therefore monotonicity of powers of $2$ gives $2^2\le 2^{K(c_0+1)\ell(m)+(K+2)}$. As $2^2=4$, this is the claimed bound.
