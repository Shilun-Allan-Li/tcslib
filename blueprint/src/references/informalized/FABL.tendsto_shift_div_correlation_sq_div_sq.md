<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/GaussianQuadrantAsymptotics.lean :: FABL.tendsto_shift_div_correlation_sq_div_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Shifted Quotient Limit

**Claim.** For every real $\rho$ with $0<\rho<1$, as $t\to+\infty$, $((t-1)/\rho)^2/t^2$ tends to $1/\rho^2$.

**Proof.** The constant function with value $1$ tends to $1$, while $t^{-1}\to0$ as $t\to+\infty$. Subtracting these limits gives $1-t^{-1}\to1$. Squaring and dividing by the constant $\rho^2$ then gives $(1-t^{-1})^2/\rho^2\to1/\rho^2$. For every nonzero $t$, the expression in the claim equals this last expression, since $(t-1)/t=1-t^{-1}$. The two functions therefore agree eventually, which preserves the limit.
