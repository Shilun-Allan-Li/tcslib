<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Orthogonality.lean :: BooleanAnalysis.GaussianSpace.integral_id_mul_polynomial_affine_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Gaussian Integration by Parts

**Claim.** For every real polynomial $p$ and real numbers $a,b$, the standard Gaussian integral of $y\,p(a+by)$ equals $b$ times the standard Gaussian integral of $p'(a+by)$.

**Proof.** Apply the polynomial Gaussian integration-by-parts identity to the composite polynomial $q(X)=p(a+bX)$, in the reversed form $\int Xq(X)\,d\gamma=\int q'(X)\,d\gamma$. The chain rule gives $q'(X)=b p'(a+bX)$, while $q(X)=p(a+bX)$. Pulling the constant $b$ out of the integral gives the stated equality.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_polynomial_derivative_standardGaussian`.
