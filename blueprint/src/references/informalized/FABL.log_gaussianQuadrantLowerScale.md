<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.log_gaussianQuadrantLowerScale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithm of the Gaussian Lower Scale

**Claim.** For $0<\rho<1$ and $t>0$, the logarithm of the scaled Gaussian lower expression equals $\log C-t^2/(1+\rho)-2\log t$, where $C$ is the stated positive constant.

**Proof.** The constant $C$ is positive by the positivity result for the Gaussian quadrant lower constant (gaussianQuadrantLowerConstant_pos), and the exponential factor is positive. Also $t^2>0$. Thus the logarithm rules for a quotient and a product apply: the logarithm of the numerator product is the sum of the logarithms, the logarithm of the exponential is its exponent, and $\log(t^2)=2\log t$. Substituting these identities gives the claimed expression; rearranging the terms completes the equality.

**Key facts.** `FABL.gaussianQuadrantLowerConstant_pos`.
