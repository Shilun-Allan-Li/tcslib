<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Orthogonality.lean :: BooleanAnalysis.GaussianSpace.integral_hermite_succ_mul_polynomial_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hermite Polynomial Integration by Parts

**Claim.** For every natural number $k$ and real polynomial $p$, integration against the standard Gaussian measure sends the product of the degree-$(k+1)$ Hermite polynomial and $p$ to the integral of the degree-$k$ Hermite polynomial times $p'$.

**Proof.** Write $H$ for the degree-$k$ Hermite polynomial with real coefficients. Gaussian integration by parts applied to the polynomial $Hp$ gives $\int (Hp)'\,d\gamma=\int xHp\,d\gamma$ (the polynomial integration-by-parts identity, `integral_polynomial_derivative_standardGaussian`). By the product rule, the left side is the sum of the integrals of $H'p$ and $Hp'$. Polynomial evaluation respects products, so the right side is the integral of $(xH)p$. Rearranging yields $\int (xH-H')p\,d\gamma=\int Hp'\,d\gamma$. The Hermite recurrence identifies $xH-H'$ with the degree-$(k+1)$ Hermite polynomial, proving the formula. All these polynomial integrals exist because polynomial evaluations are integrable under the standard Gaussian measure (`integrable_polynomial_eval_standardGaussian`).

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_polynomial_derivative_standardGaussian`, `BooleanAnalysis.GaussianSpace.integrable_polynomial_eval_standardGaussian`.
