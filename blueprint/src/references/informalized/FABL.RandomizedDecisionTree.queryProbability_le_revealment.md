<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.queryProbability_le_revealment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query probability bounded by revealment

**Claim.** For every coordinate $i$, its probability of being queried under independent inputs of law $\pi$ is at most the revealment of $T$ under $\pi$.

**Proof.** The existence of coordinate $i$ makes the coordinate set nonempty. Revealment is therefore the supremum of the query probabilities over all coordinates. Since $i$ belongs to that set, its query probability is at most this supremum.
