<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.hasDerivAt_standardGaussianDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standard Gaussian Density Derivative

**Claim.** At every real $t$, the standard Gaussian density is differentiable with derivative $-t$ times its value at $t$.

**Proof.** Write the standard Gaussian density as $(2\pi)^{-1/2}\exp(-x^2/2)$, using the density formula (`FABL.standardGaussianDensity_formula`). The exponent $-x^2/2$ has derivative $-t$ at $t$, by the power rule and constant multiplication. The chain rule for the exponential, followed by multiplication by the constant $(2\pi)^{-1/2}$, therefore gives derivative $-t(2\pi)^{-1/2}\exp(-t^2/2)=-t\,\phi(t)$.

**Key facts.** `FABL.standardGaussianDensity_formula`.
