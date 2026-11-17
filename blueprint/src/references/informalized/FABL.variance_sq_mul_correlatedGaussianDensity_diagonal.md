<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.variance_sq_mul_correlatedGaussianDensity_diagonal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Diagonal Correlated Gaussian Density

**Claim.** For $0<\rho<1$ and $t\in\mathbb R$, the correlated Gaussian density on the diagonal satisfies the stated identity after multiplication by $(1-\rho^2)^2$.

**Proof.** Use the explicit formula for the correlated Gaussian density (`correlatedGaussianDensity_formula`) and set both coordinates equal to $t$. Write $v=1-\rho^2$, which is positive by `correlationResidualVariance_pos`. The exponent in the density becomes $-(2t^2-2\rho t^2)/(2v)=-t^2/(1+\rho)$, since $v=(1-\rho)(1+\rho)$. For the prefactor, split $\sqrt{2\pi v}$ as $\sqrt{2\pi}\sqrt v$, valid because both factors are positive. Multiplying the two reciprocal square-root factors by $v^2$ leaves $v^{3/2}/(2\pi)$, which is exactly $(\sqrt v)^3/(2\pi)$. Combining this prefactor with the simplified exponential gives the identity.

**Key facts.** `FABL.correlatedGaussianDensity_formula`, `FABL.correlationResidualVariance_pos`.
