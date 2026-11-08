<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.osssCounterexampleRandomizedTreeAt_queryProbability_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of querying coordinate zero

**Claim.** For every real $t$, the specified tree, viewed as a randomized tree with a trivial seed and a uniform input, queries coordinate $0$ with probability $1$.

**Proof.** The query probability is the seed average of the deterministic tree's structural query probability (`RandomizedDecisionTree.queryProbability_eq_seed_structural`). The seed is trivial, so its point-mass expectation evaluates that probability at the unique tree (`pmfExpectation_pure`). That tree begins by querying coordinate $0$ on every input, hence the probability is $1$.

**Key facts.** `FABL.RandomizedDecisionTree.queryProbability_eq_seed_structural`, `FABL.pmfExpectation_pure`.
