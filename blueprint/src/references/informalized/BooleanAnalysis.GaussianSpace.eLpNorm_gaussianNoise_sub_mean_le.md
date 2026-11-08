<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Continuity.lean :: BooleanAnalysis.GaussianSpace.eLpNorm_gaussianNoise_sub_mean_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered Gaussian Noise Difference Bound

**Claim.** For $rho\in[-1,1]$ and integrable $f$, the $L^1$ norm of its Gaussian noise minus its Gaussian mean is at most the product Gaussian $L^1$ norm of $f(\rho x+\sqrt{1-\rho^2}\,y)-f(y)$.

**Proof.** For each fixed $x$, the integrand $f(\rho x+\sqrt{1-\rho^2}\,y)-f(y)$ is integrable in $y$: the first term is integrable by the noise-integrand result, and the second by the hypothesis on $f$. Its integral is therefore the noise of $f$ at $x$ minus the Gaussian mean of $f$. The resulting function on pairs $(x,y)$ is almost everywhere strongly measurable. Indeed, the Gaussian endpoint map preserves product Gaussian measure, giving measurability of the composed first term, while the second term is measurable by pullback along the second projection. Apply the contraction of integration in an $L^p$ norm ($eLpNorm_integral_prod_le$) with $p=1$ to bound the norm of this average by the product-space norm of the integrand.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_gaussianNoise_integrand`, `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianEndpoint`, `BooleanAnalysis.GaussianSpace.eLpNorm_integral_prod_le`.
