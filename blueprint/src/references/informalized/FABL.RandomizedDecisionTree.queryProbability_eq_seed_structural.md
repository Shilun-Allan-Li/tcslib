<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.RandomizedDecisionTree.queryProbability_eq_seed_structural -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Probability from Structural Probabilities

**Claim.** The probability that a randomized decision tree queries coordinate $i$ under independent inputs of law $\pi$ equals the seed-law average of the structural query probabilities of its deterministic trees.

**Proof.** Write the randomized query probability as the input expectation of the seed expectation of the indicator that coordinate $i$ is queried. Interchanging these finite averages (`pmfExpectation_comm`) makes this the seed expectation of each deterministic tree’s input-based query probability. For each seed, that deterministic probability equals its structural query probability (`FiniteDecisionTree.deterministicQueryProbability_eq_structural`). Averaging these equalities over the seed gives the claim.

**Key facts.** `FABL.pmfExpectation_comm`, `FABL.FiniteDecisionTree.deterministicQueryProbability_eq_structural`.
