<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.gaussianConditionalSlope_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square of the Gaussian Conditional Slope

**Claim.** For every $\rho\in(0,1)$, the square of the Gaussian conditional slope satisfies $\bigl(\frac{1-\rho}{\sqrt{1-\rho^2}}\bigr)^2=\frac{1-\rho}{1+\rho}$.

**Proof.** The correlation residual variance is positive (\texttt{FABL.correlationResidualVariance\_pos}), so the square of its square root is $1-\rho^2$. Squaring the defining quotient of the slope therefore gives $(1-\rho)^2/(1-\rho^2)$. Since $1-\rho^2=(1-\rho)(1+\rho)$ and both factors are nonzero for $0<\rho<1$, cancellation yields $(1-\rho)/(1+\rho)$.

**Key facts.** `FABL.correlationResidualVariance_pos`.
