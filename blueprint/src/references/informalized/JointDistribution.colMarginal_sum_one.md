<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/CCE.lean :: JointDistribution.colMarginal_sum_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Column Marginals Sum to One

**Claim.** The column marginals of a joint distribution sum to one.

**Proof.** Substitute the definition of each column marginal into the sum over columns. This gives the sum of the profile probabilities with the order of summation reversed. Interchanging the two finite sums yields the defining total-probability sum, which is one.
