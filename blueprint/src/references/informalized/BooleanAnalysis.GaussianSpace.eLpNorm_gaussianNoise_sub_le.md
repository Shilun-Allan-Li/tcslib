<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Continuity.lean :: BooleanAnalysis.GaussianSpace.eLpNorm_gaussianNoise_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Noise Difference Norm Bound

**Claim.** For $\rho\in[-1,1]$ and integrable $f$, the $L^1$ norm of the difference between its Gaussian noise and $f$ is at most the product Gaussian $L^1$ norm of the corresponding pointwise noise difference.

**Proof.** For each fixed $x$, integrability of the noise integrand and of the constant function $f(x)$ allows the integral of their difference over $y$ to be written as the noise integral minus $f(x)$; the Gaussian measure is a probability measure, so the constant integrates to itself. Thus the function whose $L^1$ norm is on the left is the average, over $y$, of the function $(x,y)\mapsto f(\rho x+\sqrt{1-\rho^2}\,y)-f(x)$. This product-space function is almost everywhere strongly measurable: the Gaussian endpoint map preserves the product Gaussian measure, so composing $f$ with it preserves integrability and almost everywhere strong measurability, and the second term is measurable by pulling back along the first projection. The contraction of integration in an $L^p$ norm ($eLpNorm_integral_prod_le$) with $p=1$ now bounds the norm of the average by the product-space norm, as required.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_gaussianNoise_integrand`, `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianEndpoint`, `BooleanAnalysis.GaussianSpace.eLpNorm_integral_prod_le`.
