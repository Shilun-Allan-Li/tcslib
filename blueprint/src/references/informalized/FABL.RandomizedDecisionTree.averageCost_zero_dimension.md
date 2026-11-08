<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.RandomizedDecisionTree.averageCost_zero_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Average Cost in Dimension Zero

**Claim.** For a randomized decision tree on inputs with zero coordinates, the average query cost is zero for every probability distribution on the finite input alphabet.

**Proof.** The sum of the query probabilities over all coordinates equals the average query cost (`sum_queryProbability_eq_averageCost`). In dimension zero there are no coordinates, so this sum is an empty sum and equals zero. Hence the average query cost is zero.

**Key facts.** `FABL.RandomizedDecisionTree.sum_queryProbability_eq_averageCost`.
