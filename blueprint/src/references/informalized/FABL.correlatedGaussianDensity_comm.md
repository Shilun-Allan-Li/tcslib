<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.correlatedGaussianDensity_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of the Correlated Gaussian Density

**Claim.** For $0<\rho<1$, the correlated Gaussian density at $(z_1,z_2)$ equals its value at $(z_2,z_1)$.

**Proof.** Use the explicit density formula (`correlatedGaussianDensity_formula`) for each ordering of the arguments. The prefactor is unchanged, and the exponent has numerator $z_1^2-2\rho z_1z_2+z_2^2$, which is symmetric under exchanging $z_1$ and $z_2$. The two expressions therefore agree.

**Key facts.** `FABL.correlatedGaussianDensity_formula`.
