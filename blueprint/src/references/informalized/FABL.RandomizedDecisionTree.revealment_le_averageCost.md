<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.revealment_le_averageCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Revealment bounded by average cost

**Claim.** The largest, over coordinates, of the probability that the tree queries that coordinate on an independent product-distributed input is at most the expected number of queries under that input distribution.

**Proof.** If there are coordinates, revealment is their supremum. For each coordinate, its query probability is at most the sum of all coordinate query probabilities: every term is nonnegative, and the coordinate in question is among the terms. The sum equals average cost ($\texttt{FABL.RandomizedDecisionTree.sum\_queryProbability\_eq\_averageCost}$), so the supremum is at most average cost. If there are no coordinates, revealment is $0$, which is at most average cost by its nonnegativity ($\texttt{FABL.RandomizedDecisionTree.averageCost\_nonneg}$).

**Key facts.** `FABL.RandomizedDecisionTree.averageCost_nonneg`, `FABL.RandomizedDecisionTree.queryProbability_nonneg`, `FABL.RandomizedDecisionTree.sum_queryProbability_eq_averageCost`.
