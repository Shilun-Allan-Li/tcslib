<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.averageCost_ofDeterministic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Cost of a Deterministic Tree

**Claim.** The randomized decision tree that selects a given deterministic tree with probability one has average query cost equal to that tree’s deterministic average query cost.

**Proof.** The average-cost-as-seed-expectation identity (`averageCost_eq_seedExpectation`) expresses the randomized average cost as the seed-law expectation of the selected tree’s deterministic average cost. For the construction in question, the seed space consists of one point, and its law assigns probability one to that point. Thus the expectation evaluates the deterministic average cost at the sole seed, giving the claimed equality (`pmfExpectation_pure`).

**Key facts.** `FABL.RandomizedDecisionTree.averageCost_eq_seedExpectation`, `FABL.pmfExpectation_pure`.
