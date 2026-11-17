<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.parityAndAcceptanceProbability_le_twoPowInv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity acceptance probability upper bound

**Claim.** For every integer $k\ge2$, the specified parity acceptance probability $p_k$ is at most $\tfrac12+2^{-k}$.

**Proof.** The inverse power $2^{-k}$ is nonnegative. Since $(-1)^k$ is either $1$ or $-1$, the factor $\frac34-\frac14(-1)^k$ is respectively $\frac12$ or $1$, and in either case is at most $1$. Multiplying by the nonnegative inverse power and adding $\frac12$ gives the claimed bound.
