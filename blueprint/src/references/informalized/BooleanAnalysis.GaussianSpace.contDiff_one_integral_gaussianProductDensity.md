<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDifferentiation.lean :: BooleanAnalysis.GaussianSpace.contDiff_one_integral_gaussianProductDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Differentiability of product Gaussian averages

**Claim.** For measurable $f$ bounded in absolute value by $1$ and any positive variance $v$, the product Gaussian average as a function of the mean vector is continuously differentiable.

**Proof.** At each mean vector $c$, the derivative formula for the product Gaussian average identifies its Fréchet derivative with the integral of $f(z)$ times the derivative of the product density at $c$. This proves differentiability at every $c$. The resulting derivative, viewed as a function of $c$, is continuous by the continuity theorem for the integrated product-density derivative. Hence the average is continuously differentiable.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasFDerivAt_integral_gaussianProductDensity`, `BooleanAnalysis.GaussianSpace.continuous_integral_gaussianProductDensityDerivative`.
