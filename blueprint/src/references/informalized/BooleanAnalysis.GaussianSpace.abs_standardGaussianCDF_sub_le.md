<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Halfspace.lean :: BooleanAnalysis.GaussianSpace.abs_standardGaussianCDF_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz Bound for the Gaussian Distribution Function

**Claim.** For all real $x,y$, the standard Gaussian distribution function satisfies $|\Phi(x)-\Phi(y)|\le\varphi(0)|x-y|$.

**Proof.** The standard Gaussian CDF has derivative equal to its density at each point (`hasDerivAt_standardGaussianCDF`). That density is positive (`standardGaussianPDF_pos`) and is bounded above everywhere by its value at zero (`standardGaussianPDF_le_at_zero`). Thus the derivative norm along the interval from $x$ to $y$ is at most $\varphi(0)$. The mean-value estimate for a differentiable function on the convex real line now gives the asserted Lipschitz bound.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianCDF`, `BooleanAnalysis.GaussianSpace.standardGaussianPDF_le_at_zero`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`.
