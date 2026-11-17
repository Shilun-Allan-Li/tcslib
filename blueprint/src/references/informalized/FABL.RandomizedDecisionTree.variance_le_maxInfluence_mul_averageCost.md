<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.RandomizedDecisionTree.variance_le_maxInfluence_mul_averageCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance bound by maximum influence

**Claim.** The variance of the sign-valued function is at most its maximum coordinate influence times the randomized decision tree’s average cost.

**Proof.** The OSSS inequality bounds the variance by the sum over coordinates of query probability times coordinate influence (`osss`). Each coordinate influence is at most the maximum coordinate influence, and each query probability is nonnegative. Therefore each summand is at most the query probability times the maximum influence, so the sum is at most the maximum influence times the sum of the query probabilities. The sum of query probabilities equals average cost (`sum_queryProbability_eq_averageCost`), giving the result.

**Key facts.** `FABL.RandomizedDecisionTree.osss`, `FABL.productInfluence_le_maximum`, `FABL.RandomizedDecisionTree.queryProbability_nonneg`, `FABL.RandomizedDecisionTree.sum_queryProbability_eq_averageCost`.
