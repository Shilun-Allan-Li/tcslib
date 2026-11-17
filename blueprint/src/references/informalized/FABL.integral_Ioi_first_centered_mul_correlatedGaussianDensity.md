<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.integral_Ioi_first_centered_mul_correlatedGaussianDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered Correlated Gaussian Tail Integral

**Claim.** For $0<\rho<1$ and real $z_2,t$, the integral over $z_1>t$ of $(z_1-\rho z_2)$ times the correlated Gaussian density equals $(1-\rho^2)$ times that density evaluated at $(t,z_2)$.

**Proof.** Use the symmetry of the correlated Gaussian density to exchange its two coordinates. With $z_2$ fixed, the density then factors as the standard Gaussian density at $z_2$ times the Gaussian density in $z_1$ with mean $\rho z_2$ and variance $1-\rho^2$. The integral is therefore the first factor times the centered Gaussian tail integral. The centered Gaussian tail formula says that integrating $(x-\mu)$ times a Gaussian density of mean $\mu$ and positive variance $v$ over $x>t$ gives $v$ times its density at $t$ (`integral_Ioi_centered_mul_gaussianPDFReal`). Here $v=1-\rho^2>0$ (`correlationResidualVariance_pos`). Recombine the two density factors and use symmetry once more to obtain the stated value.

**Key facts.** `FABL.correlatedGaussianDensity_comm`, `FABL.correlationResidualVariance_pos`, `FABL.integral_Ioi_centered_mul_gaussianPDFReal`.
