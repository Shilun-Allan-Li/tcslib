<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications.lean :: BooleanAnalysis.Hypercontractivity.product_smallSet_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise stability bound for an indicator

**Claim.** For the finite product space and parameters satisfying the theorem's hypotheses, the noise stability of the indicator of any event $A$ is at most $P(A)^{2-2/q}$.

**Proof.** Separate the endpoint $q=2$ from the strict case. When $q=2$, the rate constraint gives $\rho\le1$. The stability sum is bounded above by the first norm of the noisy indicator: on $A$ this follows from $u\le|u|$, and off $A$ the indicator vanishes. First-norm contraction then bounds it by the first norm of the indicator, which is $P(A)$. This is the required exponent at $q=2$. When $q>2$, take square roots in the rate constraint to obtain $\sqrt{\rho}\le (1/\sqrt{q-1})\lambda^{1/2-1/q}$. Product hypercontractivity at rate $\sqrt{\rho}$ bounds the second norm of the noisy indicator by its norm at exponent $q/(q-1)$. Stability at rate $\rho$ equals the square of that noisy second norm. Squaring the norm bound and using the indicator norm formula yields $P(A)^{2/(q/(q-1))}=P(A)^{2-2/q}$, as required.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.noise_norm_one_le`, `BooleanAnalysis.Hypercontractivity.product_hypercontractivity`, `BooleanAnalysis.Hypercontractivity.product_stability_sq_eq_norm_noise_sq`, `BooleanAnalysis.Hypercontractivity.product_indicator_norm_sq`.
