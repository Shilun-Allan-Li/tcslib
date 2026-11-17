<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.card_stableInfluencePolynomial_zero_ge_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting influential coordinates

**Claim.** If the variance of a function on the product space is at most $1$, then for every $0<\varepsilon\le 1$, at most $1/\varepsilon$ coordinates have stable influence at parameter $0$ at least $\varepsilon$.

**Proof.** Let $J$ be the set of coordinates whose stable influence at parameter $0$ is at least $\varepsilon$. By the definition of $J$, summing these influences gives at least $|J|\varepsilon$. At parameter $0$, only multi-indices of order one contribute: the zero-parameter identity for stable influence gives this restriction (\texttt{stableInfluencePolynomial_zero}). Summing over coordinates therefore counts each order-one Fourier coefficient squared exactly once, since such an index has exactly one nonzero coordinate. The resulting sum is at most the sum of squared Fourier coefficients over all nonconstant indices, because all terms are nonnegative. By the Fourier variance identity (\texttt{variance_eq_sum_sq_fourierCoeff}), this latter sum is the variance, at most $1$. Since each influence is nonnegative, the sum over $J$ is bounded by the sum over all coordinates. Thus $|J|\varepsilon\le 1$, and division by the positive number $\varepsilon$ yields $|J|\le 1/\varepsilon$.

**Key facts.** `FABL.FiniteFourierBasis.stableInfluencePolynomial_zero`, `FABL.multiIndexOrder_cast_eq_sum_indicator`, `FABL.FiniteFourierBasis.variance_eq_sum_sq_fourierCoeff`.
