<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.correlatedGaussianDensity_formula -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlated Gaussian Density Formula

**Claim.** For $0<\rho<1$, the correlated Gaussian density is $\displaystyle \frac{1}{\sqrt{2\pi}\sqrt{2\pi(1-\rho^2)}}\exp\!\left(-\frac{z_1^2-2\rho z_1z_2+z_2^2}{2(1-\rho^2)}\right)$.

**Proof.** Expand the definition as the product of the standard normal density at $z_1$ and the normal density at $z_2$ with mean $\rho z_1$ and variance $1-\rho^2$. The residual variance is positive (`correlationResidualVariance_pos`), so the conditional Gaussian formula applies. Multiplying the normalizing factors gives the displayed prefactor. Combining the exponentials adds their exponents, and expanding $(z_2-\rho z_1)^2$ yields the numerator $z_1^2-2\rho z_1z_2+z_2^2$ over $2(1-\rho^2)$.

**Key facts.** `FABL.coe_correlationResidualVariance`, `FABL.correlationResidualVariance_pos`.
