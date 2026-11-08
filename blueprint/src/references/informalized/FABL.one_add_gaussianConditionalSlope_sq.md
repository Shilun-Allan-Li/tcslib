<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.one_add_gaussianConditionalSlope_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Gaussian conditional slope identity

**Claim.** For $0<\rho<1$, if $s=(1-\rho)/\sqrt{1-\rho^2}$, then $1+s^2=\frac{2}{1+\rho}$.

**Proof.** Use the squared-slope identity $s^2=(1-\rho)/(1+\rho)$ (`gaussianConditionalSlope_sq`). Since $1+\rho\ne0$, putting the terms over the common denominator gives $1+s^2=1+(1-\rho)/(1+\rho)=2/(1+\rho)$.

**Key facts.** `FABL.gaussianConditionalSlope_sq`.
