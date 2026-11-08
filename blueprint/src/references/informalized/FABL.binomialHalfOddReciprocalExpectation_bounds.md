<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.binomialHalfOddReciprocalExpectation_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd reciprocal binomial expectation bounds

**Claim.** For every natural number $m$, if $J$ has the binomial distribution with $m$ trials and success probability $1/2$, then $\displaystyle\frac{1-2^{-(m+1)}}{m+1}\le \mathbb E[1/(2J+1)]\le\frac{1-2^{-(m+1)}}{m+1}+\frac{4}{(m+1)(m+2)}$.

**Proof.** First express the expectation as its finite binomial sum using `binomialHalfOddReciprocalExpectation_eq_sum`. For the lower bound, compare each summand with the corresponding even-denominator summand: since $2j+1<2j+2$, their reciprocals satisfy $1/(2j+2)\le1/(2j+1)$. The binomial weights are nonnegative, so summing preserves this inequality. The even reciprocal sum is exactly $(1-2^{-(m+1)})/(m+1)$ by `binomialHalfEvenReciprocalSum_eq`.

For the upper bound, split each odd reciprocal as bounded by the even reciprocal plus an error term: $1/(2j+1)\le1/(2j+2)+1/((j+1)(j+2))$. Multiplication by the nonnegative binomial weights and summation bounds the expectation by the even reciprocal sum plus the weighted error sum. The even sum has the same exact value as above, while `binomialHalfTwoSuccReciprocalSum_le` bounds the error sum by $4/((m+1)(m+2))$. Combining these gives the stated upper bound.

**Key facts.** `FABL.binomialHalfOddReciprocalExpectation_eq_sum`, `FABL.binomialHalfEvenReciprocalSum_eq`, `FABL.binomialHalfTwoSuccReciprocalSum_le`.
