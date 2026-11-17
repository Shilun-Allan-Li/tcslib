<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.deriv_neg_log_one_sub_biasedMinusProbabilityPolynomial_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative-log derivative lower bound

**Claim.** Under the stated monotonicity, nonconstancy, interval, ordering, and critical-value hypotheses, the derivative at $p$ of the negative logarithm of one minus the biased-minus probability polynomial is at least $1/(2p)$.

**Proof.** Write $F(t)$ for the biased-minus probability polynomial. Strict increase on $[0,1]$ and $p_c\le p$, together with $F(p_c)=1/2$, give $F(p)\ge 1/2$. Also, the polynomial lies strictly between $0$ and $1$ at $p$, so $1-F(p)>0$. Its logistic derivative bound gives $F'(p)\ge F(p)(1-F(p))/(p(1-p))$. Since $F(p)\ge 1/2$ and $1-p\le 1$, this implies $F'(p)\ge (1-F(p))/(2p)$. The derivative of $-\log(1-F(t))$ is $F'(p)/(1-F(p))$; the denominator is positive, so the preceding inequality yields the claimed bound. The derivative formula for $F$ in terms of total influence (`hasDerivAt_biasedMinusProbabilityPolynomial_eq_totalInfluence`) supplies the derivative used in this chain-rule computation.

**Key facts.** `FABL.strictMonoOn_biasedMinusProbabilityPolynomial`, `FABL.biasedMinusProbabilityPolynomial_mem_Ioo`, `FABL.deriv_biasedMinusProbabilityPolynomial_ge_logistic`, `FABL.hasDerivAt_biasedMinusProbabilityPolynomial_eq_totalInfluence`.
