<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/CCE.lean :: JointDistribution.rowMarginal_sum_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row Marginals Sum to One

**Claim.** The row marginals of a joint distribution sum to one.

**Proof.** Summing the row marginal over all row actions gives the iterated sum of profile probabilities, first over columns and then over rows. This is exactly the total-probability sum in the definition of a joint distribution, hence equals one.
