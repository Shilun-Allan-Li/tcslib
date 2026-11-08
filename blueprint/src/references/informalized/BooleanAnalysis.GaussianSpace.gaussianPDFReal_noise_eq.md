<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Density.lean :: BooleanAnalysis.GaussianSpace.gaussianPDFReal_noise_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian density identity under noise

**Claim.** When $v+\rho^2=1$ and $v>0$, the Gaussian density with mean $\rho x$ and variance $v$ factors as the stated multiplier times the standard Gaussian density.

**Proof.** Expand the two quadratic expressions in the exponents. The variance relation $v+\rho^2=1$ gives the identity $-(z-\rho x)^2/(2v)=x^2/2-(\rho z-x)^2/(2v)-z^2/2$. Exponentiating turns this sum into a product of exponentials. The remaining normalization factors rearrange to the displayed square-root multiplier, yielding the density identity.
