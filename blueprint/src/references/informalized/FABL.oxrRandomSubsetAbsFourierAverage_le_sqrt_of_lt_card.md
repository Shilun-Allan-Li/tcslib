<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.oxrRandomSubsetAbsFourierAverage_le_sqrt_of_lt_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier average above a size threshold

**Claim.** If $\delta\in[0,1]$, $\delta\le\frac12$, the function is bounded by one in absolute value, and $t<|S|$, then the expected absolute Fourier coefficient at $S\cap K$ is at most $\sqrt{(1-\delta)^t}$.

**Proof.** Let $q=1-\delta$. The assumptions imply $q\in[0,1]$ and $\delta\le q$. First bound the expected square of the Fourier coefficient. Reindexing the intersection average gives a sum over $J\subseteq S$, with weight $q^{|J|}(1-q)^{|S\setminus J|}$ (`FABL.expectDeltaRandomSubset_intersection_eq_sum`). Since $1-q=\delta\le q$, this weight is at most $q^{|J|+|S\setminus J|}=q^{|S|}$. Each squared coefficient is nonnegative, so the whole sum is bounded by $q^{|S|}$ times the sum of all squared Fourier coefficients. Parseval's inequality for a function bounded by one bounds that sum by one (`FABL.BoundedCubeFunction.sum_sq_fourierCoeff_le_one`). As $t<|S|$ and $0\le q\le1$, we have $q^{|S|}\le q^t$. Thus the expected square is at most $q^t$. Finally, Cauchy–Schwarz for the subset weights bounds the expected absolute value by the square root of the expected square (`FABL.expectDeltaRandomSubset_abs_le_sqrt_sq`); monotonicity of square root gives the stated bound.

**Key facts.** `FABL.expectDeltaRandomSubset_intersection_eq_sum`, `FABL.BoundedCubeFunction.sum_sq_fourierCoeff_le_one`, `FABL.expectDeltaRandomSubset_abs_le_sqrt_sq`.
