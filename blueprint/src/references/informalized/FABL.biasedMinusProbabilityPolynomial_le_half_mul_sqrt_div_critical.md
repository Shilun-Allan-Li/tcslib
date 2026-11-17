<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.biasedMinusProbabilityPolynomial_le_half_mul_sqrt_div_critical -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical square-root bound

**Claim.** If $0\le p_0\le p_c<1$ and the polynomial at $p_c$ is $1/2$, then its value at $p_0$ is at most $\frac12\sqrt{p_0/p_c}$.

**Proof.** If $p_0=0$, the endpoint value is zero, proving the inequality. Otherwise $p_0>0$. The logarithmic critical comparison gives $\log F(p_0)-\frac12\log p_0\le\log(1/2)-\frac12\log p_c$. The polynomial is positive at $p_0$ by its strict interior range (biasedMinusProbabilityPolynomial_mem_Ioo), so this inequality can be rearranged as $\log F(p_0)\le\log(1/2)+\frac12\log(p_0/p_c)$. The ratio is positive; exponentiating the right side identifies it as $\frac12\sqrt{p_0/p_c}$.

**Key facts.** `FABL.biasedMinusProbabilityPolynomial_endpoints`, `FABL.log_biasedMinusProbabilityPolynomial_le_critical`, `FABL.biasedMinusProbabilityPolynomial_mem_Ioo`.
