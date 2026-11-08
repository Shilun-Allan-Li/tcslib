<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.osssCounterexampleRandomizedTreeAt_queryProbability_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of querying coordinate one

**Claim.** For every real $t$, the specified tree, viewed as a randomized tree with a trivial seed and a uniform input, queries coordinate $1$ with probability $3/4$.

**Proof.** The probability can be computed by averaging the tree's structural query probability over its seed (`RandomizedDecisionTree.queryProbability_eq_seed_structural`). Since the tree has a trivial seed with point-mass law, this average is just the structural query probability of the given deterministic tree (`pmfExpectation_pure`). Under a uniform sign input, averaging over each queried sign is the equally weighted average of its two values (`pmfExpectation_uniformSign_eq_average`). For coordinate $1$, if the first sign is $-1$, the tree queries coordinate $1$ immediately; if it is $1$, the tree queries coordinate $1$ only when the queried coordinate $2$ is $1$. These cases have probabilities $1/2$ and $(1/2)(1/2)$, respectively, giving $3/4$.

**Key facts.** `FABL.RandomizedDecisionTree.queryProbability_eq_seed_structural`, `FABL.pmfExpectation_pure`, `FABL.pmfExpectation_uniformSign_eq_average`.
