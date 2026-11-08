<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell.lean :: BooleanAnalysis.GaussianSpace.gaussianHalfspaceStability_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Half-measure Gaussian stability

**Claim.** For every real $\rho$, Gaussian halfspace stability at measure parameter $1/2$ equals the probability that two independent standard real Gaussians $G,H$ satisfy $G\le 0$ and $\rho G+\sqrt{1-\rho^2}\,H\le 0$.

**Proof.** At $\alpha=1/2$, neither of the boundary branches in the definition of Gaussian halfspace stability applies: $1/2>0$ and $1/2<1$. The standard Gaussian distribution function at zero is $1/2$ (\texttt{standardGaussianCDF\_zero}); the quantile identity says that whenever the distribution function at $t$ is $\alpha$, the quantile at $\alpha$ is $t$ (\texttt{standardGaussianQuantile\_eq}). Thus the relevant quantile is zero. Substituting it into the defining event gives exactly the quadrant event defining the stated probability, so the two quantities agree.

**Key facts.** `BooleanAnalysis.GaussianSpace.standardGaussianCDF_zero`, `BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_eq`.
