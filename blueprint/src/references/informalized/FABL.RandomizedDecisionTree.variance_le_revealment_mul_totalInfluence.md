<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.RandomizedDecisionTree.variance_le_revealment_mul_totalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance bound by revealment

**Claim.** The variance of the sign-valued function is at most the randomized decision tree’s revealment times the function’s total influence.

**Proof.** Apply the OSSS inequality to bound variance by the sum, over coordinates, of query probability times coordinate influence (`osss`). Each coordinate’s query probability is at most the revealment, and each coordinate influence is nonnegative. Thus each summand is bounded by revealment times that coordinate’s influence. Summing these bounds gives revealment times the sum of the coordinate influences, which is the total influence.

**Key facts.** `FABL.RandomizedDecisionTree.osss`, `FABL.RandomizedDecisionTree.queryProbability_le_revealment`, `FABL.productInfluence_nonneg`.
