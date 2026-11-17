<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/CorrelationImmunityBounds.lean :: FABL.correlationImmune_not_resilient_three_mul_succ_le_two_mul_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension Bound for Correlation-Immune Functions

**Claim.** If a Boolean function is $k$th-order correlation immune but not $k$-resilient, and is nonconstant, then $3(k+1)\le 2n$.

**Proof.** Assume for contradiction that $2n<3(k+1)$. Since the function is correlation immune but not resilient, its mean cannot be zero: otherwise it would be balanced and hence resilient. The mean equals its empty-set Fourier coefficient (`mean_eq_fourierCoeff_empty`), so that coefficient is nonzero. The function is also nonconstant. The characterization of zero Fourier regularity by constancy (`isFourierRegular_zero_iff_exists_const`) then ensures that some nonempty set $S$ has a nonzero Fourier coefficient.

In fact, every nonempty set $T$ with nonzero Fourier coefficient must have $k<|T|$: if $|T|\le k$, correlation immunity forces the coefficient to be zero. Thus $k+1\le |T|$, and the contradictory assumption implies $2n<3|T|$ for each such $T$. Apply the large-support Fourier-square identity (`fourierCoeff_sq_eq_two_mul_empty_mul_of_large_support`) to $S$. It says that the $S$-coefficient of the pointwise square of the function is twice the product of its empty-set coefficient and its $S$-coefficient.

But the function takes values in signs, so its pointwise square is identically $1$. Its Fourier coefficient at the nonempty set $S$ is therefore the mean of the monomial on $S$, which is zero by the monomial expectation formula (`expect_monomial`). The identity would then make twice the product of two nonzero coefficients zero, a contradiction. Hence $3(k+1)\le 2n$.

**Key facts.** `FABL.mean_eq_fourierCoeff_empty`, `FABL.isFourierRegular_zero_iff_exists_const`, `FABL.fourierCoeff_sq_eq_two_mul_empty_mul_of_large_support`, `FABL.expect_monomial`.
