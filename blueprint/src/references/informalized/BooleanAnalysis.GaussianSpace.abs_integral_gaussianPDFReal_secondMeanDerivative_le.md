<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.abs_integral_gaussianPDFReal_secondMeanDerivative_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Second Mean Derivative Bound

**Claim.** If $|f(z)|\le1$ everywhere, then for nonzero variance $v\ge0$ and any mean $c$, the absolute Gaussian integral of the second mean-derivative kernel times $f$ is at most $2/v$.

**Proof.** Rewrite the integrand as the Gaussian density times $((z-c)^2/v^2-1/v)f(z)$. The norm of an integral is bounded by the integral of the absolute value of its integrand. Since $|f(z)|\le1$, the absolute value of the remaining factor is at most $|(z-c)^2/v^2-1/v|$, which in turn is at most $(z-c)^2/v^2+1/v$. Integrating this bound uses the centered-square moment identity (BooleanAnalysis.GaussianSpace.integral_centered_sq_gaussianReal): the expectation of $(z-c)^2$ is $v$, and the Gaussian measure has total mass one. The resulting sum is $1/v+1/v=2/v$.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_centered_sq_gaussianReal`.
