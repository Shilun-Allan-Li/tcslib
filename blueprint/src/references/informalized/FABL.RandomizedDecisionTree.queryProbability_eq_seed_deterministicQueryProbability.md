<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.RandomizedDecisionTree.queryProbability_eq_seed_deterministicQueryProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Probability as a Seed Average

**Claim.** The probability that a randomized decision tree queries a given coordinate under independent inputs with law $\pi$ equals the seed-law average of the corresponding query probability for each deterministic tree.

**Proof.** Expand the randomized query probability as an expectation over inputs of the seed-averaged indicator that the coordinate is queried. The finite-expectation interchange law (`pmfExpectation_comm`) reverses the order of averaging, yielding the seed average of the input-average indicator. That inner input average is precisely the deterministic tree’s query probability under the product input law.

**Key facts.** `FABL.pmfExpectation_comm`.
