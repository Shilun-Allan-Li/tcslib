<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/ProfileCalculus.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianBivariateSlope_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Gaussian slope

**Claim.** For fixed $\rho$ and $b$, the function of $p$ given by the Gaussian CDF at $(\Phi^{-1}(b)-\rho\Phi^{-1}(p))/\sqrt{1-\rho^2}$ has the derivative specified in the statement at each $a\in(0,1)$.

**Proof.** Apply the chain rule to the standard Gaussian CDF composed with the displayed affine rescaling of the Gaussian quantile. The CDF derivative is the standard Gaussian density (`hasDerivAt_standardGaussianCDF`). At the interior point $a$, the quantile has derivative equal to the reciprocal of the Gaussian isoperimetric profile (`hasDerivAt_standardGaussianQuantile`). Multiplying by the derivative of the affine rescaling gives the claimed expression; simplification of the resulting factors yields the stated formula.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianCDF`, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianQuantile`.
