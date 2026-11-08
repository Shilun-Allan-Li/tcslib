<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.gaussianBivariateStability_zero_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing at a Zero Threshold

**Claim.** For every correlation parameter $\rho$ and threshold $\alpha$, the bivariate stability $B_\rho(\alpha,0)$ is zero.

**Proof.** Unfold the definition and consider the set being measured. Any point in this set would have to satisfy $\Phi(\rho x+\sqrt{1-\rho^2}y)\le 0$. But the standard Gaussian CDF is strictly positive at every real input (`standardGaussianCDF_pos`), so this inequality is impossible. The set is therefore empty, and its measure, hence the bivariate stability, is zero.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_pos`.
