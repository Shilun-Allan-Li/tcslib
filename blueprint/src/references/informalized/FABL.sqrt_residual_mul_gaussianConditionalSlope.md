<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.sqrt_residual_mul_gaussianConditionalSlope -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Conditional Slope Identity

**Claim.** For $0<\rho<1$, with $c(\rho)=(1-\rho)/\sqrt{1-\rho^2}$, one has $\sqrt{1-\rho^2}\,c(\rho)=1-\rho$.

**Proof.** By the positivity of the residual variance (`correlationResidualVariance_pos`), $1-\rho^2>0$, so its square root is nonzero. Substituting the definition of $c(\rho)$, the left side is $\sqrt{1-\rho^2}\,(1-\rho)/\sqrt{1-\rho^2}$. Cancellation of the nonzero square-root factor leaves $1-\rho$.

**Key facts.** `FABL.correlationResidualVariance_pos`.
