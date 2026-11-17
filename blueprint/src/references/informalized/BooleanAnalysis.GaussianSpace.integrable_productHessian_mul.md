<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductBounds.lean :: BooleanAnalysis.GaussianSpace.integrable_productHessian_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of Gaussian Hessian products

**Claim.** For a measurable function bounded in absolute value by $1$, the stated Gaussian Hessian expression multiplied by that function is integrable under the product Gaussian measure.

**Proof.** The absolute value of the Hessian expression times any scalar of absolute value at most $1$ is bounded by the sum of the two centered coordinate squares divided by $2v^2$, plus $1/v$ (`abs_productHessian_mul_le`). This dominating function is integrable by `integrable_productHessian_bound`. The expression being integrated is measurable: the coordinate expression is measurable, and its product with the given measurable function remains measurable. The domination criterion for integrability therefore gives the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.abs_productHessian_mul_le`, `BooleanAnalysis.GaussianSpace.integrable_productHessian_bound`.
