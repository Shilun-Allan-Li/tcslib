<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.totalStableInfluence_one_sub_lower_of_dependsOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence Lower Bound

**Claim.** If a balanced Boolean function depends only on coordinates in $J$, and $|J|\leq k$, then for $0<\delta<1$ its stable influences over $J$ sum to at least $(1-\delta)^{k-1}$.

**Proof.** Set $\rho=1-\delta$, so $0\leq\rho\leq1$. The real-valued sign representation still depends only on $J$ (`dependsOn_toReal_iff`). Balance and the variance formula for Boolean functions imply that its variance is $1$ (`variance_eq_four_mul_probabilities`). Express total stable influence in Fourier form (`totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff`). Since the variance is $1$, the nonempty Fourier coefficients have squared sum $1$ (`variance_eq_sum_sq_fourierCoeff`). For each nonempty set $S$ with nonzero coefficient, dependence forces $S\subseteq J$ (`fourierCoeff_eq_zero_of_dependsOn_of_not_subset`), hence $|S|\leq k$. Also $|S|\geq1$. Because $0\leq\rho\leq1$, these bounds give $\rho^{k-1}\leq\rho^{|S|-1}\leq |S|\rho^{|S|-1}$. Multiplying by the nonnegative squared coefficient and summing shows total stable influence is at least $\rho^{k-1}$. Finally, every coordinate outside $J$ has zero stable influence: any Fourier set containing it is not a subset of $J$, so its coefficient vanishes by the same dependence fact. Thus total stable influence equals the sum over $J$, proving the claim.

**Key facts.** `FABL.dependsOn_toReal_iff`, `FABL.variance_eq_four_mul_probabilities`, `FABL.totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff`, `FABL.variance_eq_sum_sq_fourierCoeff`, `FABL.fourierCoeff_eq_zero_of_dependsOn_of_not_subset`.
