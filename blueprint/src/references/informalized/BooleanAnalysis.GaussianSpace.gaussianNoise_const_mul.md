<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of Gaussian Noise

**Claim.** For any real $\rho,c$ and function $f$, the Gaussian noise image of $cf$ is pointwise $c$ times the Gaussian noise image of $f$.

**Proof.** Fix an input $x$. The integrand defining the noise image of $cf$ is the constant multiple $c$ of the integrand defining the noise image of $f$. The constant-multiple rule for integration pulls $c$ outside the integral, giving the asserted equality at each $x$.
