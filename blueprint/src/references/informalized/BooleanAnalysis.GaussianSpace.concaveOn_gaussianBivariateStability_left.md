<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/ProfileCalculus.lean :: BooleanAnalysis.GaussianSpace.concaveOn_gaussianBivariateStability_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concavity of bivariate Gaussian stability

**Claim.** For $\rho,b\in(0,1)$, the bivariate Gaussian stability probability, viewed as a function of $a$, is concave on $[0,1]$.

**Proof.** First, $0<\rho<1$ also gives $-1<\rho<1$. The stability function is continuous on the square of probabilities $[0,1]^2$ by the continuity result for bivariate Gaussian stability (continuousOn_gaussianBivariateStability); fixing the second coordinate at $b$ gives continuity in $a$ on $[0,1]$. For interior $a$, its derivative is the Gaussian distribution function evaluated at $(q_b-\rho q_a)/\sqrt{1-\rho^2}$, where $q_t$ denotes the standard Gaussian quantile (hasDerivAt_gaussianBivariateStability_left). The derivative of this slope is $-\rho$ times the Gaussian density at the same argument, divided by $\sqrt{1-\rho^2}$ times the Gaussian isoperimetric profile at $a$ (hasDerivAt_gaussianBivariateSlope_left). This second derivative is nonpositive: $\rho>0$, the density is positive (standardGaussianPDF_pos), the square-root factor is positive, and the isoperimetric profile is the positive density evaluated at a quantile. Thus the slope is nonincreasing, and the derivative criterion for concavity, together with continuity on the closed interval, proves concavity on $[0,1]$.

**Key facts.** `BooleanAnalysis.GaussianSpace.continuousOn_gaussianBivariateStability`, `BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianBivariateStability_left`, `BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianBivariateSlope_left`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`.
