<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.endpointThresholdLogRatio_monotoneOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Endpoint Threshold Log Ratio

**Claim.** Under the stated monotonicity, nonconstancy, endpoint, and critical-point hypotheses, the endpoint threshold log ratio is monotone on $[1/2,b]$.

**Proof.** Apply the derivative criterion for monotonicity on a convex interval. The function is continuous on $[1/2,b]$: the biased-minus probability polynomial is continuous (`continuous_biasedMinusProbabilityPolynomial`), and throughout this interval its values lie strictly between $0$ and $1$ (`biasedMinusProbabilityPolynomial_mem_Ioo`), so the logarithm of one minus that polynomial is defined and continuous. Also $p<1$ throughout the interval, so the other logarithm is defined and continuous. At an interior point $p$, the same strict bounds and $p<1$ permit differentiation of both logarithmic terms. The derivative of the first term is the derivative of $-\log(1-B_f(p))$, while the derivative of the second is $-1/(2(1-p))$. The supplied endpoint derivative bound (`deriv_neg_log_one_sub_probability_ge_endpoint`), applicable because $p\ge p_c$, says the first derivative is at least $1/(2(1-p))$. Their sum is therefore nonnegative. The derivative criterion now gives monotonicity on the whole closed interval.

**Key facts.** `FABL.continuous_biasedMinusProbabilityPolynomial`, `FABL.biasedMinusProbabilityPolynomial_mem_Ioo`, `FABL.deriv_neg_log_one_sub_probability_ge_endpoint`.
