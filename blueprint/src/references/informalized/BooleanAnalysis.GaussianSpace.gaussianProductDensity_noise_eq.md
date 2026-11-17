<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Density.lean :: BooleanAnalysis.GaussianSpace.gaussianProductDensity_noise_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Density Under Noise Decomposition

**Claim.** If $s\ne0$ and $s^2+\rho^2=1$, then for all $x,y\in\mathbb R^n$ the product of Gaussian densities with means $\rho x_i$ and variance $s^2$ equals the stated prefactor and exponential terms times the product of standard Gaussian densities at $y_i$.

**Proof.** The variance $s^2$ is nonzero because $s\ne0$. Apply the one-dimensional noise identity (`gaussianPDFReal_noise_eq`) in each coordinate, using $s^2+\rho^2=1$. This writes each factor as the common square-root ratio times $\exp(x_i^2/2)$, times $\exp(-(\rho y_i-x_i)^2/(2s^2))$, times the standard Gaussian density at $y_i$. Multiplying over coordinates collects the common ratio to the $n$th power and combines the exponential factors by summing their exponents. The identity for that sum of exponents (`gaussianNoise_exponent_sum`) rewrites it as $-\frac12\sum_i((x_i-\rho y_i)/s)^2$, giving the claimed formula.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianPDFReal_noise_eq`, `BooleanAnalysis.GaussianSpace.gaussianNoise_exponent_sum`.
