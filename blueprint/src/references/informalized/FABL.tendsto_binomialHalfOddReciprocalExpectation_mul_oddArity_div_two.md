<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.tendsto_binomialHalfOddReciprocalExpectation_mul_oddArity_div_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd reciprocal binomial expectation limit

**Claim.** For a binomial random variable $J_m$ with parameters $m$ and $1/2$, the quantity $\frac{2m+1}{2}\,\mathbb{E}[1/(2J_m+1)]$ tends to $1$.

**Proof.** The expectation is bounded below by $(1-2^{-(m+1)})/(m+1)$ and above by that same term plus $4/((m+1)(m+2))$ (`binomialHalfOddReciprocalExpectation_bounds`). After multiplying by $(2m+1)/2$, the lower bound tends to $1$: its geometric correction tends to zero, while $(2m+1)/(2(m+1))$ tends to $1$. The added upper-bound error tends to zero, since $(2m+1)/(m+1)$ stays bounded and $1/(m+2)$ tends to zero. Thus both bounds tend to $1$, and the squeeze theorem gives the asserted limit.

**Key facts.** `FABL.binomialHalfOddReciprocalExpectation_bounds`.
