<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_lt_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian CDF Is Below One

**Claim.** For every real $t$, the standard Gaussian distribution function satisfies $\Phi(t)<1$.

**Proof.** Strict monotonicity of the standard Gaussian CDF gives $\Phi(t)<\Phi(t+1)$. A CDF is at most $1$ at every point, so $\Phi(t+1)\le1$. Combining these inequalities proves the claim.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_strictMono`.
