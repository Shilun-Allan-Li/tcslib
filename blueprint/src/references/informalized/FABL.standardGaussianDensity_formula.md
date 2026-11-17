<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.standardGaussianDensity_formula -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standard Gaussian density formula

**Claim.** The standard Gaussian density at $t$ is $(\sqrt{2\pi})^{-1}\exp(-t^2/2)$.

**Proof.** Substituting mean $0$ and variance $1$ into the defining formula for the Gaussian density removes the mean shift and variance factor. The remaining exponent $-(1/2)t^2$ is exactly $-t^2/2$, giving the stated expression.
