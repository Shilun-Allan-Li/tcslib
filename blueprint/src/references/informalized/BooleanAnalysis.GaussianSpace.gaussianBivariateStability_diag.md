<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.gaussianBivariateStability_diag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Diagonal Stability Identity

**Claim.** For all real numbers $\rho$ and $\alpha$, the Gaussian bivariate stability at $(\rho,\alpha,\alpha)$ equals the Gaussian halfspace stability at $(\rho,\alpha)$.

**Proof.** Split into three ranges for $\alpha$. If $\alpha\le 0$, positivity of the Gaussian distribution function makes the first defining inequality impossible, so the bivariate event is empty and both quantities are zero. If $1\le\alpha$, the distribution function is always less than $1$, so both inequalities in the bivariate event hold everywhere; its measure is one, matching the halfspace stability in this range. In the remaining case, $0<\alpha<1$. The CDF at the Gaussian quantile equals $\alpha$, and strict monotonicity of the CDF therefore converts each inequality of the form $\Phi(u)\le\alpha$ into $u\le\Phi^{-1}(\alpha)$. Thus the bivariate event is exactly the threshold event used in the halfspace definition, and the two quantities agree.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_pos`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_lt_one`, `BooleanAnalysis.GaussianSpace.gaussianBivariateStability_eq_threshold`.
