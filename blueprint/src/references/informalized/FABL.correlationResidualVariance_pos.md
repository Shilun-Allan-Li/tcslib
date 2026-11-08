<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.correlationResidualVariance_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive residual variance

**Claim.** For every real correlation parameter $\rho$ with $0<\rho<1$, the residual variance $1-\rho^2$ is positive.

**Proof.** Since $0<\rho<1$, multiplying the strict inequality $\rho<1$ by the positive number $\rho$ gives $\rho^2<\rho$. Together with $0<\rho$, this implies $\rho^2<1$, hence $1-\rho^2>0$.
