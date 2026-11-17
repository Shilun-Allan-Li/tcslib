<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.tendsto_log_gaussianQuadrantAtThreshold_div_tailLog -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Quadrant Tail Logarithmic Rate

**Claim.** For fixed $0<\rho<1$, the logarithm of the joint Gaussian upper-quadrant probability, divided by the logarithm of the standard Gaussian upper tail, tends to $2/(1+\rho)$.

**Proof.** Write $a=2/(1+\rho)$. For all $t\ge1$, the joint probability is bounded above by the standard upper tail raised to the power $a$ (`gaussianQuadrantAtThreshold_le_tail_rpow`), and bounded below by a positive constant times $\exp(-t^2/(1+\rho))/t^2$ (`gaussianQuadrantAtThreshold_lower_exp_div_sq`). The lower scale is positive because its constant is positive (`gaussianQuadrantLowerConstant_pos`). The standard tail lies strictly between zero and one (`standardGaussianUpperTail_pos`, `standardGaussianUpperTail_lt_one`), so its logarithm is negative. Taking logarithms in the upper bound gives $\log\Lambda_\rho(t)\le a\log Q(t)$. Taking logarithms in the lower bound gives a lower bound for $\log\Lambda_\rho(t)$ by the logarithm of the lower scale. Dividing both inequalities by the negative quantity $\log Q(t)$ reverses their directions and traps the desired ratio between $a$ and the lower-scale logarithmic ratio. The latter tends to $a$ (`tendsto_log_gaussianQuadrantLowerScale_div_tailLog`); the squeeze theorem now gives the asserted limit.

**Key facts.** `FABL.gaussianQuadrantAtThreshold_le_tail_rpow`, `FABL.gaussianQuadrantLowerConstant_pos`, `FABL.gaussianQuadrantAtThreshold_lower_exp_div_sq`, `FABL.standardGaussianUpperTail_pos`, `FABL.standardGaussianUpperTail_lt_one`, `FABL.tendsto_log_gaussianQuadrantLowerScale_div_tailLog`.
