<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.correlatedGaussianDensity_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Correlated Gaussian Density

**Claim.** For every $0<\rho<1$ and $z_1,z_2\in\mathbb{R}$, the correlated Gaussian density at $(z_1,z_2)$ is strictly positive.

**Proof.** The density is the product of two Gaussian densities: the standard Gaussian density at $z_1$ and a Gaussian density at $z_2$ with mean $\rho z_1$ and variance $1-\rho^2$. The Gaussian density is strictly positive whenever its variance is positive. The first variance is $1$, and the residual variance is nonzero (by `correlationResidualVariance_ne_zero ρ`); by its definition it is nonnegative, so it is positive. Both factors are therefore positive, and their product is positive.

**Key facts.** `FABL.correlationResidualVariance_ne_zero`.
