<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianMillsRatio.lean :: FABL.hasDerivAt_standardGaussianDensity_mills -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standard Gaussian Density Derivative

**Claim.** At every real $t$, the standard Gaussian density is differentiable with derivative $-t$ times its value at $t$.

**Proof.** Use the density formula $\phi(x)=(2\pi)^{-1/2}\exp(-x^2/2)$ (`FABL.standardGaussianDensity_formula_mills`). The exponent $-x^2/2$ has derivative $-t$ at $t$. Applying the chain rule to the exponential and multiplying by the constant $(2\pi)^{-1/2}$ gives $-t\phi(t)$.

**Key facts.** `FABL.standardGaussianDensity_formula_mills`.
