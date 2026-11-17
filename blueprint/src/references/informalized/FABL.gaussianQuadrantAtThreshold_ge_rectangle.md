<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.gaussianQuadrantAtThreshold_ge_rectangle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Rectangle Lower Bound

**Claim.** For $0<\rho<1$, the Gaussian quadrant probability at threshold $t$ is at least the product of the standard Gaussian mass of $(t,t+1/t)$ and the upper tail at the conditional threshold $s_\rho t$, where $s_\rho=(1-\rho)/\sqrt{1-\rho^2}$.

**Proof.** The quadrant probability at threshold $t$ is the measure of the upper right quadrant under the correlated Gaussian measure (\texttt{gaussianQuadrantAtThreshold\_eq\_measure}). By the change of variables defining that measure, it is the product standard Gaussian measure of the preimage of this quadrant. The map is measurable by continuity (\texttt{continuous\_gaussianCorrelationMap}), and the quadrant is open, hence measurable (\texttt{isOpen\_gaussianUpperRightQuadrant}). The product measure of the rectangle $(t,t+1/t)\times(s_\rho t,\infty)$ factors as the product of its two marginal measures; the second factor is the standard Gaussian upper tail at $s_\rho t$ (\texttt{standardGaussianUpperTail\_eq\_measureReal\_Ioi}). It remains to check that the rectangle maps into the quadrant. If $u>t$ and $v>s_\rho t$, the first coordinate is $u>t$. For the second, positivity of $\sqrt{1-\rho^2}$ (from \texttt{correlationResidualVariance\_pos}) gives $\sqrt{1-\rho^2}v>\sqrt{1-\rho^2}s_\rho t=(1-\rho)t$ (\texttt{sqrt\_residual\_mul\_gaussianConditionalSlope}). Also $\rho u>\rho t$, since $\rho>0$. Adding yields $\rho u+\sqrt{1-\rho^2}v>t$. Monotonicity of measure now gives the asserted lower bound.

**Key facts.** `FABL.gaussianQuadrantAtThreshold_eq_measure`, `FABL.continuous_gaussianCorrelationMap`, `FABL.isOpen_gaussianUpperRightQuadrant`, `FABL.standardGaussianUpperTail_eq_measureReal_Ioi`, `FABL.correlationResidualVariance_pos`, `FABL.sqrt_residual_mul_gaussianConditionalSlope`.
