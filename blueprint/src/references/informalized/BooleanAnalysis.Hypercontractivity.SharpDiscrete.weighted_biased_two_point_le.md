<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointContraction.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_biased_two_point_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp weighted two point contraction

**Claim.** For $1<p<2$ and $0<\lambda<1/2$, the weighted two point quadratic expression is bounded by the weighted $p$-moment raised to $2/p$, with coefficient $\rho(p/(p-1),\lambda)^2$.

**Proof.** Set $\alpha=\lambda^{1/p}$ and $\beta=(1-\lambda)^{1/p}$. These satisfy $0<\alpha<\beta$ and $\alpha^p+\beta^p=1$. The biased two point inequality (`SharpDiscrete.biased_two_point_le`) applied with these parameters bounds the squared weighted mean plus its variance term by the weighted $p$-moment to the power $2/p$. The coefficient identity (`SharpDiscrete.bias_coefficient_eq_radius_sq`) identifies the variance coefficient with $\rho(p/(p-1),\lambda)^2$, since $\alpha^p=\lambda$; likewise $\beta^p=1-\lambda$. Substituting these identities yields the stated inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.biased_two_point_le`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.bias_coefficient_eq_radius_sq`.
