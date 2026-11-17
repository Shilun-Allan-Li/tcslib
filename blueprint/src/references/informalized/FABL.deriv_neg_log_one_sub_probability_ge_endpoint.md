<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.deriv_neg_log_one_sub_probability_ge_endpoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Endpoint logarithmic-derivative bound

**Claim.** Under the stated hypotheses, the derivative at $p$ of $-\log(1-q_f(t))$ is at least $1/(2(1-p))$.

**Proof.** Let $F$ denote the biased-minus probability polynomial. Strict increase and the critical-value condition imply $F(p)\ge 1/2$. The polynomial also lies strictly between $0$ and $1$ at $p$, so $1-F(p)>0$. By its logistic derivative bound, $F'(p)\ge F(p)(1-F(p))/(p(1-p))$. Since $F(p)\ge 1/2$ and $p\le 1$, this is at least $(1-F(p))/(2(1-p))$. The derivative of $-\log(1-F(t))$ is $F'(p)/(1-F(p))$, giving the result. The identity expressing $F'(p)$ through total influence (`hasDerivAt_biasedMinusProbabilityPolynomial_eq_totalInfluence`) justifies the derivative computation for the logarithm.

**Key facts.** `FABL.strictMonoOn_biasedMinusProbabilityPolynomial`, `FABL.biasedMinusProbabilityPolynomial_mem_Ioo`, `FABL.deriv_biasedMinusProbabilityPolynomial_ge_logistic`, `FABL.hasDerivAt_biasedMinusProbabilityPolynomial_eq_totalInfluence`.
