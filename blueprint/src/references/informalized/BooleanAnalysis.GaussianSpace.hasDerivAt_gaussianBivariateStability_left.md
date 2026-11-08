<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/ProfileCalculus.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianBivariateStability_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of bivariate Gaussian stability

**Claim.** For $\rho\in(-1,1)$ and $a,b\in(0,1)$, the derivative in the first probability argument of bivariate Gaussian stability at $a$ is the standard Gaussian CDF evaluated at $(Q(b)-\rho Q(a))/\sqrt{1-\rho^2}$.

**Proof.** First express the bivariate stability as a conditional Gaussian integral: for probabilities in $(0,1)$, it equals the integral of $\Phi((Q(b)-\rho x)/\sqrt{1-\rho^2})$ over $x\le Q(p)$ against standard Gaussian measure (`BooleanAnalysis.GaussianSpace.gaussianBivariateStability_eq_conditional_integral`). The derivative formula for this quantile-truncated integral says that its derivative at $p=a$ is its integrand evaluated at the moving endpoint $x=Q(a)$ (`BooleanAnalysis.GaussianSpace.hasDerivAt_quantile_conditional_integral`). The stability function and this integral agree for all $p$ in a neighborhood of $a$, since that neighborhood remains inside $(0,1)$; hence they have the same derivative there. Substituting $x=Q(a)$ gives the claimed value.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasDerivAt_quantile_conditional_integral`, `BooleanAnalysis.GaussianSpace.gaussianBivariateStability_eq_conditional_integral`.
