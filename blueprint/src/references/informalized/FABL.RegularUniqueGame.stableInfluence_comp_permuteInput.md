<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.stableInfluence_comp_permuteInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence Under Coordinate Permutation

**Claim.** Permuting the input coordinates of a function by $\pi$ makes its stable influence at coordinate $i$ equal to the stable influence of the original function at $\pi^{-1}(i)$.

**Proof.** Expand stable influence as a sum over subsets containing the specified coordinate. The Fourier coefficient of the permuted function at a subset $S$ is the original Fourier coefficient at the subset obtained by applying $\pi^{-1}$ (`fourierCoeff_comp_permuteInput`). Reindex the finite subset sum by the bijection induced by $\pi^{-1}$. This bijection preserves subset cardinality, and $i\in S$ holds exactly when $\pi^{-1}(i)$ belongs to the reindexed subset. Hence the weights and squared Fourier coefficients match term by term, proving the equality.

**Key facts.** `FABL.fourierCoeff_comp_permuteInput`.
