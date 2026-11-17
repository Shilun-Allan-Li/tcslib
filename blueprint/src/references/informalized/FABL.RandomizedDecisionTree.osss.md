<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.RandomizedDecisionTree.osss -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# OSSS Variance Inequality

**Claim.** For a sign-valued function computed by a randomized decision tree, its variance is at most the sum over coordinates of the probability that the tree queries that coordinate times the function’s influence there.

**Proof.** Apply the covariance inequality with both functions equal to $f$ (`RandomizedDecisionTree.osss_covariance`). Its hypotheses hold because $f$ has sign range. The covariance of a function with itself equals its variance (`productCovariance_self`), so the resulting inequality is exactly the OSSS variance bound.

**Key facts.** `FABL.RandomizedDecisionTree.osss_covariance`, `FABL.productCovariance_self`.
