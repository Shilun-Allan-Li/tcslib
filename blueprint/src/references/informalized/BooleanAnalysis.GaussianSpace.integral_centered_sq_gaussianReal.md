<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.integral_centered_sq_gaussianReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered Second Gaussian Moment

**Claim.** For a Gaussian measure $N(c,v)$ with mean $c$ and variance $v\geq0$, the integral of $(z-c)^2$ is $v$.

**Proof.** The variance identity for a random variable states that its variance is the integral of the squared deviation from its mean. Applied to the identity random variable under $N(c,v)$, its variance is $v$, while its mean is $c$. Thus $\int(z-c)^2\,dN(c,v)(z)=v$.
