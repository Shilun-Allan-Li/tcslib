<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.biasedFourierCoeff_comp_permuteInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Coefficients Under Coordinate Permutation

**Claim.** Permuting the input by $\sigma$ changes the biased Fourier coefficient at $S$ into the coefficient of $f$ at the image of $S$ under $\sigma^{-1}$.

**Proof.** Write the coefficient as a finite sum over sign vectors and reindex that sum by the bijection that permutes coordinates using $\sigma$. The product probability mass is unchanged by this reindexing (`productProbabilityPMF_permuteInput`). The biased monomial transforms according to the permuted coordinate set (`biasedMonomial_permuteInput`); with the inverse permutation in the reindexing, the resulting set is $\sigma^{-1}(S)$. The identity that applying a permutation and its inverse to a coordinate set returns the original set (`permuteFinset_symm`) completes the change of variables.

**Key facts.** `FABL.productProbabilityPMF_permuteInput`, `FABL.biasedMonomial_permuteInput`, `FABL.permuteFinset_symm`.
