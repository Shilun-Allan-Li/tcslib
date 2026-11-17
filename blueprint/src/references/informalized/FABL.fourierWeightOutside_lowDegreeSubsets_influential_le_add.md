<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.fourierWeightOutside_lowDegreeSubsets_influential_le_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exterior Fourier weight bound

**Claim.** The Fourier weight outside the low-degree subsets of influential coordinates is at most the low-degree weight on sets not contained in those coordinates, plus the weight on sets of size greater than $k$.

**Proof.** Expand both sides as finite sums over subsets $S$ of the coordinates and combine the two sums on the right. For each $S$, split into the two possibilities: either $S$ is contained in the influential coordinates or it is not, and either $|S|\le k$ or $|S|>k$. If $S$ is contained and has size at most $k$, it belongs to the excluded low-degree family, so contributes zero on the left; it also contributes zero to both right-hand sums. If it is contained and has size greater than $k$, it contributes zero on the left and its nonnegative squared Fourier coefficient appears in the high-degree sum on the right. If it is not contained and has size at most $k$, it appears in the left exterior sum and in the low-degree outside-influential sum, with equal weight. Finally, if it is not contained and has size greater than $k$, its weight occurs on the left and in the high-degree sum on the right, as well as in the low-degree outside-influential sum only if it meets that sum's degree condition; thus the right-hand contribution is at least the left-hand one. Summing these termwise comparisons proves the inequality.
