<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/StableInfluence.lean :: FABL.totalStableInfluence_eq_sum_level -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable influence by Fourier level

**Claim.** The total stable influence at parameter $\rho$ is the sum, over levels $k$ from $0$ through $n$, of $k\rho^{k-1}$ times the Fourier weight at level $k$.

**Proof.** First use the Fourier expansion identity for total stable influence (\texttt{totalStableInfluence\_eq\_sum\_card\_mul\_rho\_pow\_mul\_sq\_fourierCoeff}), which writes it as a sum over subsets $S$ with summand $|S|\rho^{|S|-1}\widehat f(S)^2$. Group these subsets according to their cardinality $k$. Every subset of the $n$ coordinates has cardinality between $0$ and $n$, so these groups are indexed by $k=0,\ldots,n$. Within the group of size $k$, the factor $|S|\rho^{|S|-1}$ is constant and equals $k\rho^{k-1}$; factoring it out leaves the sum of squared Fourier coefficients at level $k$, namely the level-$k$ Fourier weight. Summing over the levels gives the formula.

**Key facts.** `FABL.totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff`.
