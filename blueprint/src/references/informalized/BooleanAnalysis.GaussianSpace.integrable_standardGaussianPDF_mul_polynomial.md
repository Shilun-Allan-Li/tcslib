<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Orthogonality.lean :: BooleanAnalysis.GaussianSpace.integrable_standardGaussianPDF_mul_polynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial times Gaussian density is integrable

**Claim.** For every real polynomial $p$, the product of the standard Gaussian density and $p$ is integrable with respect to Lebesgue measure.

**Proof.** Polynomial evaluation is integrable under the standard Gaussian measure by `integrable_polynomial_eval_standardGaussian`. Expressing that measure as Lebesgue measure weighted by its Gaussian density, the density-change criterion for integrability converts this into integrability of $x\mapsto\varphi(x)p(x)$ with respect to Lebesgue measure.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_polynomial_eval_standardGaussian`.
