<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/JuntaStableInfluence.lean :: FABL.pow_pred_mul_variance_le_totalStableInfluence_of_fourierDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance Bound by Total Stable Influence

**Claim.** If every nonzero Fourier coefficient of $f$ is indexed by a set of size at most $k$, and $0\le\rho\le1$, then $\rho^{k-1}\operatorname{Var}(f)$ is at most its total stable influence.

**Proof.** Rewrite total stable influence as the sum over all subsets $S$ of $|S|\rho^{|S|-1}\widehat f(S)^2$ (`totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff`). The Fourier variance formula expresses the variance as the sum of $\widehat f(S)^2$ over nonempty $S$ (`variance_eq_sum_sq_fourierCoeff`), so after multiplying by $\rho^{k-1}$ it suffices to compare the corresponding summands. The empty set contributes zero to both sides. For a nonempty set with zero Fourier coefficient the comparison is immediate. Otherwise the degree hypothesis forces $|S|\le k$ (`fourierDegree_le_iff`); since $0\le\rho\le1$, this gives $\rho^{k-1}\le\rho^{|S|-1}$. Also $|S|\ge1$, so multiplying the latter power by $|S|$ can only increase it. Multiplication by the nonnegative square $\widehat f(S)^2$ preserves the inequality. Summing these termwise comparisons proves the result.

**Key facts.** `FABL.totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff`, `FABL.variance_eq_sum_sq_fourierCoeff`, `FABL.fourierDegree_le_iff`.
