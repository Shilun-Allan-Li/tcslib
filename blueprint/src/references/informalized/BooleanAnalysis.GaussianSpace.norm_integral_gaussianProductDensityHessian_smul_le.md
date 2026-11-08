<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductHessian.lean :: BooleanAnalysis.GaussianSpace.norm_integral_gaussianProductDensityHessian_smul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrated Gaussian Hessian bound

**Claim.** For measurable $f$ with $|f(z)|\leq1$, the norm of its integral against the product Gaussian density Hessian is at most $|I|^2(2/v)$.

**Proof.** Expand the integral as a double sum indexed by coordinate pairs $(i,j)$. Its coefficient at $(i,j)$ is the Gaussian expectation of $f(z)$ times the product-Hessian kernel, and its operator factor is the tensor formed from the two coordinate projections. The expansion is given by `integral_gaussianProductDensityHessian_smul_eq_sum`. The norm of the full double sum is bounded by the sum of the absolute values of its coefficients, by the coordinate-tensor norm estimate (`norm_sum_sum_coordinateTensor_le`). For every pair $(i,j)$, the absolute value of the coefficient is at most $2/v$ by `abs_integral_productHessian_mul_le`. Summing this uniform bound over the $|I|^2$ coordinate pairs gives the claimed estimate.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_gaussianProductDensityHessian_smul_eq_sum`, `BooleanAnalysis.GaussianSpace.norm_sum_sum_coordinateTensor_le`, `BooleanAnalysis.GaussianSpace.abs_integral_productHessian_mul_le`.
