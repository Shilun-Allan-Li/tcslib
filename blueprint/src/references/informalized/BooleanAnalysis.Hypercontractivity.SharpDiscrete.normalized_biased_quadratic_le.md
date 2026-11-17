<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/TwoPointCalculus.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.normalized_biased_quadratic_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalized biased quadratic bound

**Claim.** Under the stated assumptions, the normalized biased quadratic expression is at most $((1+y)^p+(1-y)^p)^{2/p}$.

**Proof.** Set $t=(\beta-\alpha)/(\beta+\alpha)$, so $0<t<1$, and set $z=y^2$, so $0\le z\le1$. The tangent identity at the bias says that the value of the symmetric power expression at $t$ is $4/(\alpha+\beta)^2$, and its tangent slope there is $2(\beta^{p-1}-\alpha^{p-1})/(\beta-\alpha)$ (`tangent_at_bias`). An algebraic rearrangement of the left side of the desired inequality expresses it as this tangent-line value at $z$: $4/(\alpha+\beta)^2 + \frac{2(\beta^{p-1}-\alpha^{p-1})}{\beta-\alpha}(z-t^2)$. The tangent bound for biased powers (`biased_power_tangent_le`) bounds that line by $((1+\sqrt z)^p+(1-\sqrt z)^p)^{2/p}$. Since $z=y^2$, we have $\sqrt z=|y|$. If $y\ge0$, this is the required right side directly. If $y<0$, replacing $|y|$ by $-y$ interchanges the two summands, leaving their sum unchanged.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.tangent_at_bias`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.biased_power_tangent_le`.
