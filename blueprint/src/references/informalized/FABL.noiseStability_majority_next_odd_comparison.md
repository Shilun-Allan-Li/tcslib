<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityNoiseStability.lean :: FABL.noiseStability_majority_next_odd_comparison -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Stability at Consecutive Odd Dimensions

**Claim.** For $0<\rho<1$, majority stability at dimension $2m+3$ is at most its stability at dimension $2m+1$, and the inequality is strict when $\rho>0$.

**Proof.** Write $a_k$ and $b_k$ for the Fourier weight at level $k$ of majority in dimensions $2m+1$ and $2m+3$, respectively, and set $N=2m+3$. Fourier weights above the dimension vanish (\texttt{fourierWeightAtLevel_eq_zero_of_dimension_lt}), so both weight sequences can be summed through level $N$ without changing their total mass. Parseval's identity, expressed through the sum of squared Fourier coefficients (\texttt{sum_fourierWeightAtLevel_range} and \texttt{sum_sq_fourierCoeff_eq_one}), says that each total mass is $1$. Fourier expansion of stability expresses the two stabilities as $\sum_{k=0}^{N}\rho^k a_k$ and $\sum_{k=0}^{N}\rho^k b_k$ (\texttt{noiseStability_eq_sum_level_rho_pow_mul_fourierWeight}).

At each level $k<N$, the larger majority has no more Fourier weight than the smaller one, so $b_k\le a_k$ (\texttt{fourierWeightAtLevel_majority_next_odd_le_of_lt_top}). Since the total masses agree, subtracting the two weighted sums and using $\sum_k(a_k-b_k)=0$ rewrites their difference as $\sum_{k=0}^{N}(\rho^k-\rho^N)(a_k-b_k)$. For $0<\rho<1$ and $k<N$, both factors are nonnegative, by the level comparison and the fact that powers decrease with the exponent. The term at $k=N$ is zero. Thus the difference is nonnegative, proving the non-strict comparison.

For strictness when $\rho>0$, the level-one comparison is strict (\texttt{fourierWeightAtLevel_majority_next_odd_lt}), and $\rho-ho^N>0$ because $N>1$ and $\rho<1$. Hence the level-one summand is positive while all other summands are nonnegative, making the stability difference strictly positive.

**Key facts.** `FABL.fourierWeightAtLevel_eq_zero_of_dimension_lt`, `FABL.sum_fourierWeightAtLevel_range`, `FABL.sum_sq_fourierCoeff_eq_one`, `FABL.noiseStability_eq_sum_level_rho_pow_mul_fourierWeight`, `FABL.fourierWeightAtLevel_majority_next_odd_le_of_lt_top`, `FABL.fourierWeightAtLevel_majority_next_odd_lt`.
