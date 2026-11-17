<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Orthogonality.lean :: BooleanAnalysis.GaussianSpace.integral_polynomial_derivative_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Integration by Parts for Polynomials

**Claim.** For every real polynomial $p$, its derivative's standard Gaussian integral equals the standard Gaussian integral of $x p(x)$.

**Proof.** Let $\varphi$ denote the standard Gaussian density. The derivative formula $\varphi'(x)=-x\varphi(x)$ and the polynomial product rule give $(\varphi p)'=\varphi p'-x\varphi p$. The integral of this derivative is zero: the derivative is integrable, and the Gaussian density times a polynomial is integrable, so the integral-zero theorem for derivatives applies. Thus $\int \varphi p'=\int x\varphi p$. Rewriting these density-weighted integrals as integrals against the standard Gaussian measure gives the claim. The required integrability of the density times any polynomial is supplied by `integrable_standardGaussianPDF_mul_polynomial`, and the density derivative formula is `hasDerivAt_standardGaussianPDF`.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_standardGaussianPDF_mul_polynomial`, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianPDF`.
