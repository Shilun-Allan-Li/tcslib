<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.abs_integral_gaussianPDFReal_meanDerivative_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Mean Derivative Integral Bound

**Claim.** If $|f(z)|\le1$ everywhere, then for nonzero variance $v\ge0$ and any mean $c$, the absolute Gaussian mean-derivative integral is at most $1+1/v$.

**Proof.** Use the centered-square moment identity (BooleanAnalysis.GaussianSpace.integral_centered_sq_gaussianReal), which says that the Gaussian expectation of $(z-c)^2$ is $v$. The proof first bounds the integrand in absolute value, after factoring out the Gaussian density, by $((z-c)^2+1)/v$: the factor $|f(z)|$ is at most $1$, and $|z-c|\le (z-c)^2+1$. The Gaussian density integral bound (BooleanAnalysis.GaussianSpace.abs_integral_gaussianPDFReal_mul_le) then bounds the absolute integral by the expectation of $((z-c)^2+1)/v$. Integrating and using the centered-square moment gives $(v+1)/v=1+1/v$.

**Key facts.** `BooleanAnalysis.GaussianSpace.abs_integral_gaussianPDFReal_mul_le`, `BooleanAnalysis.GaussianSpace.integral_centered_sq_gaussianReal`.
