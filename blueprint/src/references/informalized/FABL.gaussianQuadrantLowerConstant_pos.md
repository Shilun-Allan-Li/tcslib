<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.gaussianQuadrantLowerConstant_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Quadrant Lower Constant

**Claim.** For every $0<\rho<1$, the Gaussian quadrant lower constant is positive.

**Proof.** The constant is $e^{-3/2}s_\rho/((1+s_\rho^2)2\pi)$. The exponential is positive, and the conditional slope $s_\rho$ is positive (\texttt{gaussianConditionalSlope\_pos}). The denominator is positive because it is a product of $1+s_\rho^2>0$ and $2\pi>0$. Thus the quotient is positive.

**Key facts.** `FABL.gaussianConditionalSlope_pos`.
