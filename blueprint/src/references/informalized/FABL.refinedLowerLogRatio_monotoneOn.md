<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.refinedLowerLogRatio_monotoneOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Refined Logarithmic Ratio

**Claim.** Let $f$ be monotone and nonconstant, and let $r,p_a\in(0,1)$. If its biased minus-probability polynomial at $p_a$ is at most $r$, then the refined logarithmic ratio is nondecreasing on $(0,p_a]$.

**Proof.** Write $P(p)$ for the biased minus-probability polynomial. On $(0,1)$, it lies strictly between $0$ and $1$ (biasedMinusProbabilityPolynomial_mem_Ioo), and it is continuous (continuous_biasedMinusProbabilityPolynomial). Strict monotonicity of $P$ on $[0,1]$ (strictMonoOn_biasedMinusProbabilityPolynomial) implies that for $0<p<p_a$, $P(p)\le P(p_a)\le r$. The ratio is continuous on $(0,p_a]$: both logarithms are defined there because $p>0$ and $P(p)>0$. It is differentiable in the interior, since the derivative of $P$ is given by the total-influence formula (hasDerivAt_biasedMinusProbabilityPolynomial_eq_totalInfluence). For such a $p$, the logistic derivative bound gives $P'(p)\ge P(p)(1-P(p))/(p(1-p))$ (deriv_biasedMinusProbabilityPolynomial_ge_logistic). As $P(p)\le r$ and $P(p)>0$, this implies $P'(p)/P(p)\ge (1-r)/(p(1-p))\ge (1-r)/p$. The derivative of $\log P(p)-(1-r)\log p$ is therefore at least zero. The derivative criterion for monotonicity on the convex interval $(0,p_a]$ yields the result.

**Key facts.** `FABL.strictMonoOn_biasedMinusProbabilityPolynomial`, `FABL.continuous_biasedMinusProbabilityPolynomial`, `FABL.biasedMinusProbabilityPolynomial_mem_Ioo`, `FABL.deriv_biasedMinusProbabilityPolynomial_ge_logistic`, `FABL.hasDerivAt_biasedMinusProbabilityPolynomial_eq_totalInfluence`.
