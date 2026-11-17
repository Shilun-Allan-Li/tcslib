<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.fourierOneNorm_majority_odd_eq_expectation_mul_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-majority norm in terms of influence

**Claim.** For every nonnegative integer $m$, the Fourier one-norm of majority on $2m+1$ sign coordinates equals the reciprocal-binomial expectation times $(2m+1)2^m$ and the odd-majority influence.

**Proof.** Start with the formula expressing the Fourier one-norm through the reciprocal-binomial expectation and the central binomial coefficient (`fourierOneNorm_majority_odd_eq_binomialExpectation`). Substitute the definition of odd-majority influence, $I_m=\binom{2m}{m}/2^{2m}$. Rearranging the powers of $2$ and the factors gives the asserted expression.

**Key facts.** `FABL.fourierOneNorm_majority_odd_eq_binomialExpectation`.
