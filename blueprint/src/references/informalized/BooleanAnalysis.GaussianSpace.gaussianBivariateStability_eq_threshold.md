<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.gaussianBivariateStability_eq_threshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quantile Threshold Representation

**Claim.** For $\alpha,\beta\in(0,1)$, Gaussian bivariate stability is the product Gaussian measure of the event that the two scalar coordinates lie below their respective Gaussian quantiles.

**Proof.** Unfold the definition of bivariate stability and show that its defining event equals the quantile threshold event. For the first coordinate, the Gaussian CDF at the quantile of $\alpha$ equals $\alpha$ (\texttt{BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_quantile}). Strict monotonicity of the CDF then says that $\Phi(z_1)\le\alpha$ holds exactly when $z_1\le\Phi^{-1}(\alpha)$. Apply the same argument to the transformed coordinate and $\beta$. The two event descriptions agree pointwise, so their product Gaussian measures agree.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_quantile`, `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_strictMono`.
