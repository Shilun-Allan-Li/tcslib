<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.abs_gaussianBivariateStability_sub_left_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-Threshold Lipschitz Bound

**Claim.** For any real $\rho,\beta$ and thresholds $\alpha,\alpha'\in[0,1]$, the absolute difference between the Gaussian bivariate stabilities at $(\alpha,\beta)$ and $(\alpha',\beta)$ is at most $|\alpha-\alpha'|$.

**Proof.** View the bivariate stability as the measure of the intersection of two events: the event that the first coordinate's Gaussian CDF is at most the threshold, and the event imposing the second CDF condition. The first coordinate projection preserves the product Gaussian measure. The bound for changing a Gaussian CDF threshold while intersecting with a fixed event (BooleanAnalysis.GaussianSpace.abs_measureReal_standardGaussianCDF_inter_sub_le) therefore applies with the second event held fixed. Since both thresholds lie in $[0,1]$, it gives the stated bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.abs_measureReal_standardGaussianCDF_inter_sub_le`.
