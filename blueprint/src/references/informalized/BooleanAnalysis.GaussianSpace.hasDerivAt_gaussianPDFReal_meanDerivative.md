<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianPDFReal_meanDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Gaussian mean score

**Claim.** For real $c,z$ and nonnegative variance $v$, the function $m\mapsto ((z-m)/v)p_v(m,z)$ has derivative at $m=c$ equal to $(((z-c)^2/v^2)-1/v)p_v(c,z)$.

**Proof.** Use the product rule on the two factors. The derivative of $(z-m)/v$ is $-1/v$, while the derivative of the Gaussian density at $m=c$ is $((z-c)/v)p_v(c,z)$ (`BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianPDFReal_mean`). Thus the product derivative is $-p_v(c,z)/v+((z-c)/v)^2p_v(c,z)$, which rearranges to the formula.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianPDFReal_mean`.
