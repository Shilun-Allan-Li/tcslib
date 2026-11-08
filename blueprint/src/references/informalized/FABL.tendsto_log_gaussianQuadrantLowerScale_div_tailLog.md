<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.tendsto_log_gaussianQuadrantLowerScale_div_tailLog -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Quadrant Lower-Scale Logarithmic Rate

**Claim.** For fixed $0<\rho<1$, the logarithm of the explicit lower scale, divided by the logarithm of the standard Gaussian upper tail, tends to $2/(1+\rho)$.

**Proof.** First divide the logarithm of the lower scale by $t^2$. For $t>0$, its logarithm expands as $\log C_\rho-t^2/(1+\rho)-2\log t$ (`log_gaussianQuadrantLowerScale`). After division by $t^2$, the constant term tends to zero (`tendsto_const_div_sq_atTop`), and the logarithmic term tends to zero (`tendsto_log_div_sq_atTop`). The middle term is the constant $-1/(1+\rho)$, so the resulting limit is $-1/(1+\rho)$. The standard upper-tail logarithm divided by $t^2$ tends to $-1/2$ (`tendsto_log_standardGaussianUpperTail_div_sq`). Taking the quotient of these two limits, whose denominator limit is nonzero, gives $2/(1+\rho)$. For sufficiently large nonzero $t$, canceling the common factor $t^2$ identifies this quotient with the stated ratio; the standard tail is positive and less than one (`standardGaussianUpperTail_pos`, `standardGaussianUpperTail_lt_one`), ensuring its logarithm is nonzero.

**Key facts.** `FABL.log_gaussianQuadrantLowerScale`, `FABL.tendsto_const_div_sq_atTop`, `FABL.tendsto_log_div_sq_atTop`, `FABL.tendsto_log_standardGaussianUpperTail_div_sq`, `FABL.standardGaussianUpperTail_pos`, `FABL.standardGaussianUpperTail_lt_one`.
