<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.exists_deterministic_averageCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Deterministic Tree with Bounded Average Cost

**Claim.** For every randomized decision tree and input distribution over a finite alphabet, some seed selects a deterministic tree whose average query cost is at most the randomized tree’s average query cost.

**Proof.** Regard the seed space as a finite probability space and assign to each seed the deterministic average cost of its selected tree. This function is integrable because the seed space is finite. The finite-space mean-value principle (`exists_le_integral`) gives a seed at which this cost is no larger than its integral. The expectation-integral identity (`pmfExpectation_eq_integral`) identifies that integral with the seed-law expectation, and the randomized average-cost identity (`averageCost_eq_seedExpectation`) identifies the latter with the randomized tree’s average cost. This proves the desired bound.

**Key facts.** `FABL.RandomizedDecisionTree.averageCost_eq_seedExpectation`, `FABL.pmfExpectation_eq_integral`.
