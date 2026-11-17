<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/CCE.lean :: JointDistribution.rowMarginal_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative Row Marginal

**Claim.** For every row action $i$, the row marginal of a joint distribution is nonnegative.

**Proof.** The row marginal is the sum, over all column actions $j$, of the probabilities $\sigma_{ij}$. Every summand is nonnegative by the defining property of a joint distribution, so the finite sum is nonnegative.
