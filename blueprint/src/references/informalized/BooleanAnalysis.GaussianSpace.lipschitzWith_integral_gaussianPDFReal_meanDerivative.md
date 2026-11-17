<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.lipschitzWith_integral_gaussianPDFReal_meanDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lipschitz Gaussian mean derivative

**Claim.** For measurable $f$ bounded in absolute value by $1$ and positive variance $v$, the Gaussian mean-derivative integral is Lipschitz in its mean with constant $2/v$.

**Proof.** Differentiate the mean-derivative integral with respect to its mean. The second mean derivative formula (`hasDerivAt_integral_gaussianPDFReal_meanDerivative`) expresses that derivative as the integral with kernel $(((z-c)^2/v^2)-1/v)p_v(c,z)$ multiplied by $f(z)$. The second-derivative integral bound (`abs_integral_gaussianPDFReal_secondMeanDerivative_le`) bounds its absolute value by $2/v$, uniformly in $c$. The derivative-bound form of the mean-value theorem now yields the asserted Lipschitz estimate.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasDerivAt_integral_gaussianPDFReal_meanDerivative`, `BooleanAnalysis.GaussianSpace.abs_integral_gaussianPDFReal_secondMeanDerivative_le`.
