<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.FiniteFourierBasis.productTotalStableInfluence_one_sub_le_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Stable Influence Bound

**Claim.** If the variance of $f$ is at most $1$ and $0<\delta<1$, then the total stable influence at correlation $1-\delta$ is at most $1/\delta$.

**Proof.** Express total stable influence as a sum over Fourier multi-indices (`productTotalStableInfluence_eq_sum`). The all-constant index contributes zero. For every other index, its support size $k$ is positive, and the elementary estimate $k(1-\delta)^{k-1}\le 1/\delta$ (`card_mul_one_sub_pow_le_inv`) bounds its weight. Multiplying by the nonnegative squared Fourier coefficient and summing bounds total stable influence by $1/\delta$ times the sum of squared nonconstant Fourier coefficients. Parseval's variance identity (`variance_eq_sum_sq_fourierCoeff`) identifies that sum with the variance. The assumed variance bound and $1/\delta>0$ then give the result.

**Key facts.** `FABL.FiniteFourierBasis.productTotalStableInfluence_eq_sum`, `FABL.card_mul_one_sub_pow_le_inv`, `FABL.FiniteFourierBasis.variance_eq_sum_sq_fourierCoeff`.

**Caveat.** The informal statement mentions a bound on the size of a thresholded coordinate set, but the formal theorem supplied proves the total stable-influence bound stated in the claim.
