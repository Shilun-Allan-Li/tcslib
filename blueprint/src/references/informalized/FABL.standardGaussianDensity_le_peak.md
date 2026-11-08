<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.standardGaussianDensity_le_peak -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum of the standard Gaussian density

**Claim.** For every real $t$, the standard Gaussian density at $t$ is at most $(\sqrt{2\pi})^{-1}$.

**Proof.** The density is $(\sqrt{2\pi})^{-1}\exp(-t^2/2)$. Since $t^2\ge0$, the exponent is nonpositive, so $\exp(-t^2/2)\le1$. The prefactor is nonnegative, and multiplying this inequality by it yields the asserted bound.
