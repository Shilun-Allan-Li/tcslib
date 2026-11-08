<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.gaussianBivariateStability_zero_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Left Threshold

**Claim.** For all real $\rho$ and $\beta$, the Gaussian bivariate stability at thresholds $(0,\beta)$ is zero.

**Proof.** At every real input the standard Gaussian CDF is strictly positive (\texttt{BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_pos}). Therefore no point can satisfy the first event condition $\Phi(x)\le0$. The defining event is empty, whose measure is zero.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianCDF_pos`.
