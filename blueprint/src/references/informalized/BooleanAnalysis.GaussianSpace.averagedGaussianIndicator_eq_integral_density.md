<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/IndicatorRegularity.lean :: BooleanAnalysis.GaussianSpace.averagedGaussianIndicator_eq_integral_density -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Density Formula for the Averaged Indicator

**Claim.** For a measurable set $A\subseteq\mathbb R^n$, a real number $u$ with $\sin u\ne0$, and $x\in\mathbb R^n$, the averaged indicator equals the integral of the indicator of $A$ against the product Gaussian density with coordinate means $\cos(u)x_i$ and variances $\sin^2(u)$.

**Proof.** Write the averaged indicator as the integral of the indicator of $A$ evaluated at the affine image $y\mapsto \cos(u)x+\sin(u)y$. Apply the affine Gaussian change-of-variables formula for product standard Gaussian measure (`integral_affine_gaussian_pi_eq_density`), taking coordinate shifts $c_i=\cos(u)x_i$ and scale $s=\sin u$. The nonzero-scale hypothesis permits this change of variables, and the resulting density is the product of the stated coordinate Gaussian densities.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_affine_gaussian_pi_eq_density`.
