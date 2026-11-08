<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Orthogonality.lean :: BooleanAnalysis.GaussianSpace.integrable_polynomial_mul_affine_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-affine Gaussian integrability

**Claim.** For real polynomials $p,q$ and real numbers $a,b$, the function $y\mapsto q(y)p(a+by)$ is integrable under the standard Gaussian measure.

**Proof.** Form the polynomial $q(X)\,p(a+bX)$, where the affine map is represented by the polynomial $a+bX$. Its evaluation at $y$ is exactly $q(y)p(a+by)$. Since every polynomial evaluation is integrable under the standard Gaussian measure (by `integrable_polynomial_eval_standardGaussian`), the stated function is integrable.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_polynomial_eval_standardGaussian`.
