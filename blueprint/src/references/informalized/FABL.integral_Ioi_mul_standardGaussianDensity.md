<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.integral_Ioi_mul_standardGaussianDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standard Gaussian Density Tail Moment

**Claim.** For every real $t$, integrating $x$ times the standard Gaussian density over $x>t$ gives the standard Gaussian density at $t$.

**Proof.** Write the standard Gaussian density as $(2\pi)^{-1/2}e^{-x^2/2}$. Pull the constant factor outside the integral and apply the Gaussian exponential tail identity: the integral of $x e^{-x^2/2}$ over $x>t$ is $e^{-t^2/2}$. Multiplying by $(2\pi)^{-1/2}$ gives exactly the density at $t$.

**Key facts.** `FABL.integral_Ioi_mul_exp_neg_half_mul_sq`.
