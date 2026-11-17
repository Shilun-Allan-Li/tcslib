<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.abs_integral_gaussianPDFReal_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Density Integral Bound

**Claim.** If $b$ is integrable against the Gaussian measure of mean $c$ and variance $v\ne0$, and $|g(z)|\le b(z)$ everywhere, then the absolute integral of $p_{c,v}(z)g(z)$ is bounded by the Gaussian expectation of $b$.

**Proof.** The Gaussian density integral formula identifies the density-weighted Lebesgue integral with the integral of $g$ against the Gaussian measure. The norm of an integral is at most the integral of the norm, so its absolute value is at most the Gaussian integral of $|g|$. Finally, the pointwise bound $|g|\le b$ and integrability of $b$ give the stated upper bound by monotonicity of integration.
