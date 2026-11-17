<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.RandomizedDecisionTree.majorityThree_averageCost_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Cost for Three-Bit Majority

**Claim.** Every zero-error randomized decision tree computing majority on three signs has average query cost at least $5/2$ when the coordinates are independent and uniformly distributed.

**Proof.** The randomized tree's average cost under the uniform product input distribution equals the expectation over its random seed of the deterministic average costs (`averageCost_eq_seedExpectation`). For each seed, the selected deterministic tree computes majority, so its average cost is at least $5/2$ (`FiniteDecisionTree.majorityThree_uniform_averageCost_ge`). The expectation of the constant $5/2$ is $5/2$ (`pmfExpectation_const`), and taking expectations preserves the pointwise lower bound (`pmfExpectation_mono`).

**Key facts.** `FABL.RandomizedDecisionTree.averageCost_eq_seedExpectation`, `FABL.pmfExpectation_const`, `FABL.FiniteDecisionTree.majorityThree_uniform_averageCost_ge`, `FABL.pmfExpectation_mono`.
