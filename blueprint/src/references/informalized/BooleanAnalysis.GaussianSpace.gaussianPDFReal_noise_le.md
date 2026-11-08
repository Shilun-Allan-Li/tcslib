<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Density.lean :: BooleanAnalysis.GaussianSpace.gaussianPDFReal_noise_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian density bound under noise

**Claim.** When $v+\rho^2=1$ and $v>0$, the density with mean $\rho x$ and variance $v$ is bounded by the stated multiple of the standard Gaussian density.

**Proof.** The exponent comparison follows from $-(z-\rho x)^2/(2v)\le x^2/2-z^2/2$. After multiplying by the positive normalization factor of the variance-$v$ density and applying monotonicity of the exponential, its density is at most $(\sqrt{2\pi v})^{-1}\exp(x^2/2-z^2/2)$. Rewriting this expression as the stated multiplier times the standard Gaussian density proves the bound.
