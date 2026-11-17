<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.gaussianQuadrantAtThreshold_lower_exp_div_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Lower Bound for the Quadrant

**Claim.** For $0<\rho<1$ and $t\ge1$, the Gaussian quadrant probability at threshold $t$ is at least $C_\rho e^{-t^2/(1+\rho)}/t^2$, where $C_\rho$ is the stated Gaussian quadrant lower constant.

**Proof.** Write $s=s_\rho=(1-\rho)/\sqrt{1-\rho^2}$. The algebraic denominator comparison for $t\ge1$ gives $s/((1+s^2)t^2)\le s/(1+s^2t^2)$ (\texttt{gaussianConditionalSlope\_div\_large\_denominator\_le}). The product of the two Gaussian densities at $t$ and $st$ is exactly $(2\pi)^{-1}e^{-t^2/(1+\rho)}$ (\texttt{standardGaussianDensity\_mul\_slope\_density}). Substituting this identity and the denominator comparison into the definition of $C_\rho$ yields that $C_\rho e^{-t^2/(1+\rho)}/t^2$ is at most the corresponding product of density factors, with the factor $e^{-3/2}$ retained. Finally, the lower Mills estimate for the quadrant probability bounds that product by the quadrant probability from below (\texttt{gaussianQuadrantAtThreshold\_lower\_mills}), giving the result.

**Key facts.** `FABL.gaussianConditionalSlope_div_large_denominator_le`, `FABL.standardGaussianDensity_mul_slope_density`, `FABL.gaussianQuadrantAtThreshold_lower_mills`.
