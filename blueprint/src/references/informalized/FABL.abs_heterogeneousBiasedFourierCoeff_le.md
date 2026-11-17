<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.abs_heterogeneousBiasedFourierCoeff_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Fourier coefficient bound

**Claim.** For coordinate biases strictly between $0$ and $1$, the absolute value of the heterogeneous biased Fourier coefficient of $f$ on $S$ is at most $\bigl(\prod_{i\in S}\sqrt{4p_i(1-p_i)}\bigr)\|f\|_\infty$.

**Proof.** Write the coefficient as the expectation, under the independent biased product law, of $f(x)$ times its standardized monomial. The triangle inequality for a finite weighted sum bounds its absolute value by the expectation of the absolute value of that product. Pointwise, $|f(x)|\le\|f\|_\infty$, so monotonicity of expectation bounds this by $\|f\|_\infty$ times the expected absolute value of the monomial. Expectation pulls out this constant factor (\texttt{FABL.pmfExpectation\_const\_mul}). The expected absolute value of the heterogeneous biased monomial is the product of the coordinate standard deviations over $S$ (\texttt{FABL.pmfExpectation\_abs\_heterogeneousBiasedMonomial}); these are $\sqrt{4p_i(1-p_i)}$. Reordering the two real factors gives the stated bound.

**Key facts.** `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_abs_heterogeneousBiasedMonomial`.
