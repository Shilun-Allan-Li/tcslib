<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.gaussianQuadrantPolylogConstant_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Polylogarithmic Constant

**Claim.** For every $0<\rho<1$, the Gaussian quadrant polylogarithmic constant is positive.

**Proof.** This constant is the product of the Gaussian quadrant lower constant and $\sqrt{2\pi}$ raised to a real power. The first factor is positive (\texttt{gaussianQuadrantLowerConstant\_pos}); the base $\sqrt{2\pi}$ is positive, so any real power of it is positive. Their product is positive.

**Key facts.** `FABL.gaussianQuadrantLowerConstant_pos`.
