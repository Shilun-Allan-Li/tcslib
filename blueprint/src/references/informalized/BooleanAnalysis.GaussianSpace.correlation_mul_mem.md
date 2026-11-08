<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Linear.lean :: BooleanAnalysis.GaussianSpace.correlation_mul_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Products preserve the correlation interval

**Claim.** If $\rho,\sigma\in[-1,1]$, then $\rho\sigma\in[-1,1]$.

**Proof.** The hypotheses give $|\rho|\le 1$ and $|\sigma|\le 1$. By multiplicativity of absolute value, $|\rho\sigma|=|\rho||\sigma|\le 1$, since both absolute values are nonnegative and at most $1$. The characterization of the interval $[-1,1]$ by absolute value now gives the result.
