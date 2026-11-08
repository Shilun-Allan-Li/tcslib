<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianPDFReal_mean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a Gaussian density in its mean

**Claim.** For real $c,z$ and nonnegative variance $v$, the Gaussian density $m\mapsto p_v(m,z)$ has derivative at $m=c$ equal to $((z-c)/v)p_v(c,z)$.

**Proof.** Write the Gaussian density as a constant normalization factor times the exponential of $-(z-m)^2/(2v)$. The normalization is independent of $m$. Differentiating the exponent gives $(z-c)/v$ at $m=c$; the chain rule for the exponential therefore yields the stated derivative. The algebra then matches this expression to the Gaussian density at $c$.
