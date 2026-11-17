<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Sharp/FiniteNoiseOptimization.lean :: BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_maximizer_stationarity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationarity at a Noise Maximizer

**Claim.** Under the stated positivity, normalization, and maximality hypotheses, the maximum satisfies $F(g)\ge1$ and each coordinate obeys $F(g)g_i^{p-1}-\rho^2g_i=(1-\rho^2)\sum_jw_jg_j$.

**Proof.** First compare the maximizer with the constant-one function. Its moment is one and its value under $F$ is one, so maximality gives $F(g)\ge1$. Fix a coordinate $i$, and perturb only that coordinate: write $h_i=1$, $h_j=0$ for $j\ne i$, and $u(t)=g+th$. The directional derivative formulas give derivatives at zero of the moment and objective: respectively $p w_i g_i^{p-1}$ and $2\bigl(\rho^2w_i g_i+(1-\rho^2)(\sum_jw_jg_j)w_i\bigr)$.

For sufficiently small $t$, the moment of $u(t)$ remains positive because it equals one at zero and is continuous there. Normalize $u(t)$ by the factor $G(u(t))^{-1/p}$. Homogeneity gives a normalized competitor whose objective is $F(u(t))/G(u(t))^{2/p}$, so maximality of $g$ makes this quotient locally maximal at zero. The quotient stationarity rule (the derivative of the numerator equals the exponent times the value times the derivative of the denominator, when the denominator equals one) therefore yields $F'(0)=(2/p)F(g)G'(0)$. Substituting the two derivative formulas and canceling the positive weight $w_i$ gives the asserted coordinate equation.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_directional_derivatives`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_noise_normalization`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.derivative_eq_mul_of_isLocalMax_quotient`.
