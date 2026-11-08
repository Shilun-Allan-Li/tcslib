<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.continuous_standardGaussianCDF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Gaussian CDF

**Claim.** The standard Gaussian distribution function $\Phi:\mathbb R\to\mathbb R$ is continuous on $\mathbb R$.

**Proof.** At each real $t$, the CDF has derivative equal to the standard Gaussian density, as stated by the derivative formula (hasDerivAt_standardGaussianCDF). Differentiability at every point implies continuity at every point, and hence continuity on $\mathbb R$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianCDF`.
