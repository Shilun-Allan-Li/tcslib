<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.RandomizedDecisionTree.pmfExpectation_symmetrizedSeedLaw -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation Under the Symmetrized Seed Law

**Claim.** Under the joint law obtained by choosing a symmetry uniformly and then a seed according to the seed law, the expectation of any real-valued function of the pair equals the uniform average over symmetries of its seed-law expectation.

**Proof.** Expand the joint law as a bind: first choose a symmetry uniformly, then map a seed to the pair consisting of that symmetry and seed. The expectation under a bind is the outer expectation of the conditional expectations (`pmfExpectation_bind`). For a fixed symmetry, expectation under the mapped seed law is the seed expectation of the function evaluated at the resulting pair (`pmfExpectation_map`). This gives the stated iterated average.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`.
