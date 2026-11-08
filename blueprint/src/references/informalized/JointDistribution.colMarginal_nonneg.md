<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/CCE.lean :: JointDistribution.colMarginal_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Column Marginal

**Claim.** For every column action $j$, the column marginal of a joint distribution is nonnegative.

**Proof.** The column marginal is the sum, over all row actions $i$, of the probabilities $\sigma_{ij}$. Each summand is nonnegative by the defining property of a joint distribution, so their finite sum is nonnegative.
