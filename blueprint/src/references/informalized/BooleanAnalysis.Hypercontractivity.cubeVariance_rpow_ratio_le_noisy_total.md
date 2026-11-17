<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.cubeVariance_rpow_ratio_le_noisy_total -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance and Noisy Fourier Energy

**Claim.** If $f$ has positive variance and $\rho>0$, then $\operatorname{Var}(f)\rho^{I(f)/\operatorname{Var}(f)}\le\sum_{S\subseteq[n]}|S|\rho^{|S|}\widehat f(S)^2$.

**Proof.** Give each subset $S$ the nonnegative weight $w(S)=\widehat f(S)^2$ when $S$ is nonempty, and weight zero when it is empty. The variance Fourier formula says that the total weight is $\operatorname{Var}(f)$ (\texttt{BooleanAnalysis.Hypercontractivity.cubeVariance_eq_sum_nonempty_fourier}). The total influence identity says that the weighted average of the degrees $|S|$ has numerator $I(f)$ (\texttt{BooleanAnalysis.totalInfluence_eq_sum_sq_deg}); the empty-set term contributes zero. Apply the weighted power-mean inequality to these weights and degrees: for positive $\rho$, the total weight times $\rho$ raised to the weighted average degree is at most the weighted sum of $\rho^{|S|}$ (\texttt{BooleanAnalysis.Hypercontractivity.FiniteNorms.weighted_rpow_mean_le}). Substituting the total weight and degree numerator gives the desired left side. Finally, for each nonempty $S$, its cardinality is at least one, so $\rho^{|S|}\widehat f(S)^2\le |S|\rho^{|S|}\widehat f(S)^2$; the empty-set term vanishes. This bounds the weighted sum by the stated noisy Fourier energy.

**Key facts.** `BooleanAnalysis.Hypercontractivity.cubeVariance_eq_sum_nonempty_fourier`, `BooleanAnalysis.totalInfluence_eq_sum_sq_deg`, `BooleanAnalysis.Hypercontractivity.FiniteNorms.weighted_rpow_mean_le`.
