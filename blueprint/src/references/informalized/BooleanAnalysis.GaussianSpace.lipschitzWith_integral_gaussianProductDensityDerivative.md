<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductHessian.lean :: BooleanAnalysis.GaussianSpace.lipschitzWith_integral_gaussianProductDensityDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz Gaussian product-density averages

**Claim.** For a finite index set $I$, the indicated integral of $f$ against the mean derivative of the product Gaussian density is Lipschitz in its mean vector with constant $2|I|^2/v$, for the stated norms.

**Proof.** The derivative of the map of mean vectors is given by integrating $f$ against the Hessian of the product Gaussian density (`hasFDerivAt_integral_gaussianProductDensityDerivative`). Its operator norm is bounded by $2|I|^2/v$ by the integrated Hessian estimate (`norm_integral_gaussianProductDensityHessian_smul_le`). Consequently the derivative norm is uniformly bounded by this constant. The mean-value estimate for a differentiable map on a normed vector space then gives the claimed Lipschitz bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasFDerivAt_integral_gaussianProductDensityDerivative`, `BooleanAnalysis.GaussianSpace.norm_integral_gaussianProductDensityHessian_smul_le`.
