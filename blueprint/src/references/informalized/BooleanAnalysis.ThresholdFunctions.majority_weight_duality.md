<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Majority.lean :: BooleanAnalysis.ThresholdFunctions.majority_weight_duality -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Fourier Weight Duality

**Claim.** For $k\leq2m+1$, the Fourier weight of majority at level $2m+2-k$ is $\frac{k}{2m+2-k}$ times its weight at level $k$.

**Proof.** If $k=0$, the level $2m+2$ lies above the dimension $2m+1$, so its weight vanishes (`weightLevel_eq_zero_of_lt`); the right-hand side vanishes as well. For positive even $k$, both levels are even, and both weights vanish (`majority_weightLevel_even`), proving the identity.

It remains to consider odd $k=2p+1$. Write the complementary odd level as $2m+2-k=2q+1$, where $p+q=m$. The explicit odd-level formula expresses the weight at each of these levels as a binomial coefficient times the square of a common normalization factor and a level-dependent binomial ratio (`majority_weightLevel_odd`). The symmetry of that ratio under exchanging $p$ and $q$ follows from `choose_div_choose_symm`. The remaining binomial factors have the ratio prescribed by $ (2q+1)\binom{2m+1}{2q+1}=(2p+1)\binom{2m+1}{2p+1}$, obtained from the symmetry of binomial coefficients and the adjacent-binomial identity. Substitution and cancellation give the factor $(2p+1)/(2q+1)=k/(2m+2-k)$, as required.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.weightLevel_eq_zero_of_lt`, `BooleanAnalysis.ThresholdFunctions.majority_weightLevel_even`, `BooleanAnalysis.ThresholdFunctions.majority_weightLevel_odd`, `BooleanAnalysis.ThresholdFunctions.choose_div_choose_symm`.
