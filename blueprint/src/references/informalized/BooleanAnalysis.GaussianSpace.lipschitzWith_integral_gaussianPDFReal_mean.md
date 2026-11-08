<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.lipschitzWith_integral_gaussianPDFReal_mean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz Gaussian averages in the mean

**Claim.** For measurable $f$ bounded in absolute value by $1$ and positive variance $v$, its Gaussian density average as a function of the mean is Lipschitz with constant $1+1/v$.

**Proof.** The Gaussian mean derivative formula (`hasDerivAt_integral_gaussianPDFReal_mean`) gives the derivative at mean $c$ as the integral of $((z-c)/v) p_v(c,z)f(z)$. The absolute value of this integral is at most $1+1/v$ by the mean-derivative integral bound (`abs_integral_gaussianPDFReal_meanDerivative_le`). Thus the derivative is bounded uniformly in $c$ by the claimed constant. The one-dimensional mean-value theorem, in its derivative-bound form, implies the Lipschitz estimate.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasDerivAt_integral_gaussianPDFReal_mean`, `BooleanAnalysis.GaussianSpace.abs_integral_gaussianPDFReal_meanDerivative_le`.
