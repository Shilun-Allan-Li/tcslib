<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.osssCounterexampleRandomizedTreeAt_queryProbability_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of querying coordinate two

**Claim.** For every real $t$, the specified tree, viewed as a randomized tree with a trivial seed and a uniform input, queries coordinate $2$ with probability $3/4$.

**Proof.** The probability equals the seed average of the tree's structural query probability (`RandomizedDecisionTree.queryProbability_eq_seed_structural`); because the seed is trivial, this reduces to the deterministic tree's structural probability (`pmfExpectation_pure`). Uniform averaging over a sign gives equal weight to its two possibilities (`pmfExpectation_uniformSign_eq_average`). If the first sign is $-1$, coordinate $2$ is queried only when coordinate $1$ is $1$; if the first sign is $1$, coordinate $2$ is queried immediately. The two disjoint cases have probabilities $(1/2)(1/2)$ and $1/2$, so the total is $3/4$.

**Key facts.** `FABL.RandomizedDecisionTree.queryProbability_eq_seed_structural`, `FABL.pmfExpectation_pure`, `FABL.pmfExpectation_uniformSign_eq_average`.
