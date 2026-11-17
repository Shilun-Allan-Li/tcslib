<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.gaussianConditionalSlope_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Gaussian Conditional Slope

**Claim.** For every $\rho\in(0,1)$, the Gaussian conditional slope $\frac{1-\rho}{\sqrt{1-\rho^2}}$ is positive.

**Proof.** By the positivity of the correlation residual variance (\texttt{FABL.correlationResidualVariance\_pos}), $1-\rho^2>0$, so its square root is positive. The numerator $1-\rho$ is positive because $\rho<1$. Their quotient is therefore positive.

**Key facts.** `FABL.correlationResidualVariance_pos`.
