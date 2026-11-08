<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Density.lean :: BooleanAnalysis.GaussianSpace.integral_gaussianNoise_densityFactorization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian noise density factorization

**Claim.** If $s\ne0$ and $s^2+\rho^2=1$, the integral of $f(\rho x+sY)$ under product standard Gaussian measure factors into the stated scalar prefactor times the standard Gaussian integral of $f(Y)$ weighted by the exponential density correction.

**Proof.** The affine Gaussian transformation $y\mapsto \rho x+sy$ sends product standard Gaussian measure to the product Gaussian measure with coordinate means $\rho x_i$ and common variance $s^2$ (\texttt{measurePreserving_gaussianAffine_pi}). Changing variables by this map rewrites the left side as an integral against that shifted, rescaled Gaussian measure. Express that measure by its product density with respect to product Lebesgue measure (\texttt{integral_pi_gaussianReal_eq_integral_smul}). The pointwise density identity (\texttt{gaussianProductDensity_noise_eq}) factors this density into the standard Gaussian product density, the scalar prefactor, and the exponential correction depending on $x$ and $y$. Pull out the scalar prefactor. Converting the remaining standard Gaussian density integral back to an integral under product standard Gaussian measure yields the formula.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianAffine_pi`, `BooleanAnalysis.GaussianSpace.integral_pi_gaussianReal_eq_integral_smul`, `BooleanAnalysis.GaussianSpace.gaussianProductDensity_noise_eq`.
