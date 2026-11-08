<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductBounds.lean :: BooleanAnalysis.GaussianSpace.abs_integral_productHessian_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Gaussian Hessian Integral Bound

**Claim.** For a bounded function with $|f|[0m\le 1$, the absolute value of its integral against the product Gaussian Hessian score is at most $2/v$.

**Proof.** First, the pointwise estimate `abs_productHessian_mul_le` bounds the absolute value of the score times $f(z)$ by the sum of a quadratic term and $1/v$. The quadratic term uses $| (z_i-c_i)(z_j-c_j) |\le ((z_i-c_i)^2+(z_j-c_j)^2)/2$, while the diagonal correction contributes at most $1/v$. The majorant is integrable under the product Gaussian measure (`integrable_productHessian_bound`), so the absolute value of the integral is bounded by the integral of this majorant. Its integral is exactly $2/v$ (`integral_productHessian_bound`), proving the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.abs_productHessian_mul_le`, `BooleanAnalysis.GaussianSpace.integrable_productHessian_bound`, `BooleanAnalysis.GaussianSpace.integral_productHessian_bound`.
