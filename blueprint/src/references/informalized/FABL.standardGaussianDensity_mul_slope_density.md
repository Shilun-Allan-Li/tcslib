<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.standardGaussianDensity_mul_slope_density -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product of densities along the conditional slope

**Claim.** For $0<\rho<1$ and $s=(1-\rho)/\sqrt{1-\rho^2}$, the product of the standard Gaussian densities at $t$ and $st$ equals $(2\pi)^{-1}\exp(-t^2/(1+\rho))$.

**Proof.** Write each density as $(\sqrt{2\pi})^{-1}$ times its exponential factor. Their product has prefactor $(\sqrt{2\pi})^{-2}=(2\pi)^{-1}$, and the exponents add to $-t^2/2-(st)^2/2$. The slope identity $s^2=(1-\rho)/(1+\rho)$ (`gaussianConditionalSlope_sq`) turns this sum into $-t^2(1+s^2)/2=-t^2/(1+\rho)$. Combining the factors gives the formula.

**Key facts.** `FABL.gaussianConditionalSlope_sq`.
