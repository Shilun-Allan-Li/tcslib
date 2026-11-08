<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductHessian.lean :: BooleanAnalysis.GaussianSpace.gaussianProductDensityHessian_dominated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrable Envelope for the Gaussian Hessian

**Claim.** For finite $I$, nonzero variance parameter $v\ge0$, and $M\ge0$, there is a nonnegative Lebesgue-integrable function that bounds the operator norm of the product Gaussian density Hessian uniformly over means whose coordinates have absolute value at most $M$.

**Proof.** The one-dimensional domination result (`gaussianPDFReal_two_derivatives_dominated`) supplies a nonnegative integrable envelope $a$ that bounds the density and the first and second derivative expressions uniformly for means in $[-M,M]$. The product of these envelopes across coordinates is integrable for product Lebesgue measure, by the finite-product integrability theorem. Expand the Hessian as a double sum of coordinate rank-one forms (`gaussianProductDensityHessian_eq_sum`). The norm of such a sum is at most the sum of the absolute values of its scalar coefficients (`norm_sum_sum_coordinateTensor_le`). For each pair of coordinates, the one-dimensional envelope bounds the corresponding coefficient by $(1+2/v)\prod_k a(z_k)$, using the density and second-derivative bounds (`abs_gaussianProductDensity_hessianCoefficient_le`). Summing over the $|I|^2$ pairs yields the claimed bound. Therefore $b(z)=|I|^2(1+2/v)\prod_k a(z_k)$ is nonnegative, integrable, and uniform in the allowed means.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianPDFReal_two_derivatives_dominated`, `BooleanAnalysis.GaussianSpace.gaussianProductDensityHessian_eq_sum`, `BooleanAnalysis.GaussianSpace.norm_sum_sum_coordinateTensor_le`, `BooleanAnalysis.GaussianSpace.abs_gaussianProductDensity_hessianCoefficient_le`.
