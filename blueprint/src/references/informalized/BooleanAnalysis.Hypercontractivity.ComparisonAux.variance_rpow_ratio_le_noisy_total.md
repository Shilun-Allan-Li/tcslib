<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.variance_rpow_ratio_le_noisy_total -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance and Noisy Total Influence

**Claim.** For a finite product probability space and a function of positive variance, every positive parameter $\rho$ satisfies $\operatorname{Var}_P(f)\rho^{I(f)/\operatorname{Var}_P(f)}\leq \sum_S |S|\rho^{|S|}\mathbb E_P[f_S^2]$.

**Proof.** Put $E(S)=\mathbb E_P[f_S^2]$ and assign weights $w(S)=E(S)$ for nonempty $S$, with $w(\varnothing)=0$. Each $E(S)$ is nonnegative, since it is an expectation of a square against nonnegative product masses. The component variance identity ( `RandomizationAux.variance_eq_sum_components`) says that these weights sum to $\operatorname{Var}_P(f)$; the total influence identity ( `RandomizationAux.totalInfluence_eq_sum_card_components`) says that their weighted average of $|S|$ is $I(f)/\operatorname{Var}_P(f)$. Apply the weighted power-mean inequality ( `FiniteNorms.weighted_rpow_mean_le`) to obtain $\operatorname{Var}_P(f)\rho^{I(f)/\operatorname{Var}_P(f)}\leq\sum_S w(S)\rho^{|S|}$. For the empty set both sides contribute zero. For every nonempty $S$, $|S|\geq1$ and $\rho^{|S|}E(S)\geq0$, so $w(S)\rho^{|S|}\leq |S|\rho^{|S|}E(S)$. Summing these inequalities gives the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.variance_eq_sum_components`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.totalInfluence_eq_sum_card_components`, `BooleanAnalysis.Hypercontractivity.FiniteNorms.weighted_rpow_mean_le`.
