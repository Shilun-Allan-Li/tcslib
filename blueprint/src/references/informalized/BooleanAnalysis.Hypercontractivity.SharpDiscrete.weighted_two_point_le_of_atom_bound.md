<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointContraction.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_two_point_le_of_atom_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two point contraction under an atom bound

**Claim.** For $q>2$, $0<\lambda<1/2$, and $\lambda\le\gamma\le1-\lambda$, the weighted two point quadratic expression with weights $\gamma,1-\gamma$ is bounded by the weighted $p$-moment raised to $2/p$, where $p=q/(q-1)$ and the coefficient is $\rho(q,\lambda)^2$.

**Proof.** Let $p=q/(q-1)$ and $\rho=\rho(q,\lambda)$; then $1<p<2$. First note that $\rho^2\le p-1$ (`SharpDiscrete.radius_sq_le_balanced`), and $\rho>0$ (`SharpDiscrete.radius_pos_lt_one`). Prove the inequality first for a weight $d$ between $\lambda$ and $1/2$. If $d<1/2$, the sharp weighted inequality at bias $d$ (`SharpDiscrete.weighted_biased_two_point_le`) applies. The radius is nondecreasing as the bias increases below one half (`SharpDiscrete.radius_mono_bias`), so the coefficient $\rho(q,\lambda)^2$ is no larger than the coefficient at bias $d$; replacing the latter by the former preserves the inequality. If $d=1/2$, apply the balanced two point inequality (`SharpDiscrete.two_point_ineq`) using $\rho^2\le p-1$, then square its nonnegative sides and rewrite the result as the desired moment inequality. Finally, if $\gamma>1/2$, apply the established case to $d=1-\gamma$ and exchange the two values $u,v$. The bounds on $\gamma$ ensure $\lambda\le1-\gamma<1/2$, and this exchange leaves both sides of the target inequality unchanged.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_sq_le_balanced`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_pos_lt_one`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.weighted_biased_two_point_le`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.radius_mono_bias`, `BooleanAnalysis.Hypercontractivity.two_point_ineq`.
