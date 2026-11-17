<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.oneThird_pow_mul_fourierWeightAtMost_le_noiseStability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree Fourier weight and noise stability

**Claim.** For a real-valued function on the $n$-dimensional sign cube, $3^{-k}$ times the sum of squared Fourier coefficients over subsets of size at most $k$ is at most its noise stability at correlation $1/3$.

**Proof.** Express noise stability as the full Fourier sum of $ho^{|S|}$ times the squared Fourier coefficient at $S$ (`noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff`), and take $\rho=1/3$. On the restricted sum where $|S|\le k$, the base $1/3$ lies between $0$ and $1$, so $(1/3)^k\le (1/3)^{|S|}$. Multiplying by the nonnegative squared coefficient and summing gives the desired comparison with the restricted part of the full Fourier sum. Every term in the full sum is nonnegative, so enlarging the index set to all subsets can only increase the sum. Combining these inequalities proves the claim.

**Key facts.** `FABL.noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff`.
