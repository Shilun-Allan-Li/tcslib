<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.averageCost_le_card_mul_revealment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Cost and Revealment

**Claim.** The average query cost is at most the number of coordinates times the largest coordinate query probability, with revealment defined to be zero when there are no coordinates.

**Proof.** The sum of the coordinate query probabilities equals the average cost (`RandomizedDecisionTree.sum_queryProbability_eq_averageCost`). Each coordinate’s query probability is at most the revealment (`RandomizedDecisionTree.queryProbability_le_revealment`). Summing these bounds over the $n$ coordinates bounds the average cost by the sum of $n$ copies of revealment; this sum is $n$ times revealment, including when there are no coordinates.

**Key facts.** `FABL.RandomizedDecisionTree.sum_queryProbability_eq_averageCost`, `FABL.RandomizedDecisionTree.queryProbability_le_revealment`.
