<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricAsymptotics.lean :: FABL.log_inv_standardGaussianDensity_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Density Logarithm

**Claim.** For every real $t>0$, the logarithm of the reciprocal of the standard Gaussian density at $t$, divided by $t$, is $t^2/2+\log t+\log\sqrt{2\pi}$.

**Proof.** The standard Gaussian density is $\exp(-t^2/2)/\sqrt{2\pi}$. Its ratio to $t$ is positive, so the logarithm of its reciprocal is the negative logarithm of that ratio. Using the logarithm laws for a quotient and a product, and $\log(\exp(-t^2/2))=-t^2/2$, this becomes $t^2/2+\log t+\log\sqrt{2\pi}$.
