<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointContraction.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_biased_radius_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Necessary radius for weighted contraction

**Claim.** If $1<p<2$, $0<\lambda<1/2$, and $\rho\ge0$ satisfy the weighted contraction inequality for every $u,v$, then $\rho\le\rho(p/(p-1),\lambda)$.

**Proof.** Represent the weights as normalized powers by setting $\alpha=\lambda^{1/p}$ and $\beta=(1-\lambda)^{1/p}$. Then $0<\alpha<\beta$ and $\alpha^p+\beta^p=1$. Use the biased two point extremizer (`SharpDiscrete.biased_two_point_extremizer`) at $u=\beta/\alpha$ and $v=\alpha/\beta$. It has unit weighted $p$-moment, and its quadratic expression is exactly one when the variance coefficient is the extremal coefficient. That coefficient equals $\rho(p/(p-1),\lambda)^2$ after applying the coefficient identity (`SharpDiscrete.bias_coefficient_eq_radius_sq`) and substituting $\alpha^p=\lambda$, $\beta^p=1-\lambda$. The assumed contraction at this same pair bounds the quadratic expression with coefficient $\rho^2$ by one. Subtract the common mean-square term from these two inequalities. The remaining variance factor $\lambda(1-\lambda)(u-v)^2$ is strictly positive, so cancellation gives $\rho^2\le\rho(p/(p-1),\lambda)^2$. Both radii are nonnegative, and $\rho\ge0$, hence the claimed comparison follows.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.biased_two_point_extremizer`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.bias_coefficient_eq_radius_sq`.
