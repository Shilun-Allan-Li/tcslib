<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.PossiblyErroneousRandomizedTree.queryProbability_ofRandomizedDecisionTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Probability Agreement

**Claim.** For each coordinate, the seed-averaged structural query probability of the randomized tree equals its query probability averaged over an independently sampled input and the seed.

**Proof.** The possibly erroneous tree obtained from the randomized decision tree has the same seed law and the same tree at each seed. Its query probability is therefore the seed expectation of each selected tree's structural query probability. The identity expressing the randomized tree's input-averaged query probability as this same seed expectation is supplied by the query-probability/structural-probability theorem (\texttt{FABL.RandomizedDecisionTree.queryProbability\_eq\_seed\_structural}). Reversing that equality gives the claim.

**Key facts.** `FABL.RandomizedDecisionTree.queryProbability_eq_seed_structural`.
