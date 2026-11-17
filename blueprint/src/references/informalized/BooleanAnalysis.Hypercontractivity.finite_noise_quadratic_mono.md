<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/General.lean :: BooleanAnalysis.Hypercontractivity.finite_noise_quadratic_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Quadratic Noise

**Claim.** For nonnegative weights summing to one and $0\le\rho\le\sigma$, the quadratic noise expression at $\rho$ is at most the same expression at $\sigma$.

**Proof.** Apply the weighted variance inequality to the sequences $r_i=w_i g_i$, $f_i=w_i g_i^2$, and weights $w_i$. Since $\sum_i w_i=1$, it gives $(\sum_i w_i g_i)^2\le\sum_i w_i g_i^2$. Also $0\le\rho\le\sigma$ implies $\rho^2\le\sigma^2$. The difference between the expression at $\sigma$ and at $\rho$ is $(\sigma^2-\rho^2)(\sum_i w_i g_i^2-(\sum_i w_i g_i)^2)$, a product of nonnegative quantities. It is therefore nonnegative, proving the inequality.
