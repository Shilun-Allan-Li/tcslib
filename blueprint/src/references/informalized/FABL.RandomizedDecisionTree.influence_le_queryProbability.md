<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.RandomizedDecisionTree.influence_le_queryProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence and Query Probability

**Claim.** For a sign-valued function computed by a zero-error randomized decision tree, its product influence at any coordinate is at most the probability that the tree queries that coordinate.

**Proof.** First express the randomized tree's query probability as the expectation, over its random seed, of the corresponding deterministic tree's structural query probability (the identity `queryProbability_eq_seed_structural`). The product influence is constant with respect to the seed, so its expectation equals itself (`pmfExpectation_const`). For each seed, the selected tree computes the function, and the deterministic bound on influence by structural query probability applies (`FiniteDecisionTree.influence_le_structuralQueryProbability`). Taking the expectation of these pointwise inequalities preserves the inequality (`pmfExpectation_mono`), giving the claimed bound.

**Key facts.** `FABL.RandomizedDecisionTree.queryProbability_eq_seed_structural`, `FABL.pmfExpectation_const`, `FABL.FiniteDecisionTree.influence_le_structuralQueryProbability`, `FABL.pmfExpectation_mono`.
