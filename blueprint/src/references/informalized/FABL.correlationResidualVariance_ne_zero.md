<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.correlationResidualVariance_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonzero residual variance

**Claim.** For every real correlation parameter $\rho$ with $0<\rho<1$, the residual variance $1-\rho^2$ is nonzero.

**Proof.** The residual variance is strictly positive by the positivity result for $0<\rho<1$ (\(\texttt{FABL.correlationResidualVariance\_pos}\)). A strictly positive real number cannot equal zero, so the residual variance is nonzero.

**Key facts.** `FABL.correlationResidualVariance_pos`.
