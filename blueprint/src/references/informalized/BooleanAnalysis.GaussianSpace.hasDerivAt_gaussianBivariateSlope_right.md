<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/ProfileCalculus.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianBivariateSlope_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Gaussian CDF composition

**Claim.** For $\rho,a\in\mathbb R$ and $b\in(0,1)$, the function $p\mapsto\Phi\!\left((Q(p)-\rho Q(a))/\sqrt{1-\rho^2}\right)$ has derivative at $b$ equal to $\varphi\!\left((Q(b)-\rho Q(a))/\sqrt{1-\rho^2}\right)/(\sqrt{1-\rho^2}\,U(b))$.

**Proof.** Apply the chain rule to the outer Gaussian CDF and the inner affine rescaling of the quantile. The standard Gaussian CDF has derivative equal to its density (the derivative formula for the standard Gaussian CDF, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianCDF`). The quantile is differentiable at $b$ with derivative $1/U(b)$ (the derivative formula for the Gaussian quantile, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianQuantile`). Subtracting the constant $\rho Q(a)$ and dividing by $\sqrt{1-\rho^2}$ multiplies that derivative by $1/\sqrt{1-\rho^2}$. Evaluating the outer density at the inner argument and multiplying these factors gives the stated expression.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianCDF`, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianQuantile`.
