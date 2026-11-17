<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Orthogonality.lean :: BooleanAnalysis.GaussianSpace.integrable_polynomial_eval_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial integrability under the standard Gaussian

**Claim.** Every real polynomial, evaluated on $\mathbb R$, is integrable under the standard Gaussian probability measure.

**Proof.** Embed the polynomial as a polynomial in one coordinate on $\mathbb R^1$. The Gaussian polynomial moment result states that evaluation of any such multivariate polynomial belongs to $L^1$ under the product standard Gaussian measure (`memLp_eval_gaussian`), since the exponent $1$ is finite. The coordinate evaluation map from the one-dimensional Gaussian space to $\mathbb R$ preserves the measure, so integrability of the embedded polynomial transfers back to integrability of the original polynomial.

**Key facts.** `BooleanAnalysis.GaussianSpace.memLp_eval_gaussian`.
