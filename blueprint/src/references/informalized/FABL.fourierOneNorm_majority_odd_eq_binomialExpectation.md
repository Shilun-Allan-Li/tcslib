<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.fourierOneNorm_majority_odd_eq_binomialExpectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm of odd majority

**Claim.** For every nonnegative integer $m$, the Fourier one-norm of majority on $2m+1$ sign coordinates equals the reciprocal-binomial expectation multiplied by $\frac{2m+1}{2^m}\binom{2m}{m}$.

**Proof.** Decompose the Fourier one-norm into the sum of the one-norms of the degree parts (`fourierOneNorm_eq_sum_degreeParts`). The even-degree parts vanish, by the vanishing result for odd majority (`fourierOneNorm_degreePart_majority_odd_eq_zero_of_even`), so the sum reduces to degrees $2j+1$ for $0\le j\le m$ (`sum_range_eq_sum_odd_of_even_eq_zero`). For each such degree, its one-norm is the stated binomial expression (`fourierOneNorm_degreePart_majority_odd`). Summing these expressions and using the finite-sum formula for the reciprocal-binomial expectation (`binomialHalfOddReciprocalExpectation_eq_sum`) gives the desired result: factor out the terms independent of $j$, and combine the remaining factor $2^{-m}$ with the other $2^{-m}$ to obtain $2^{-2m}$ in the degree sum.

**Key facts.** `FABL.fourierOneNorm_eq_sum_degreeParts`, `FABL.fourierOneNorm_degreePart_majority_odd_eq_zero_of_even`, `FABL.sum_range_eq_sum_odd_of_even_eq_zero`, `FABL.fourierOneNorm_degreePart_majority_odd`, `FABL.binomialHalfOddReciprocalExpectation_eq_sum`.
