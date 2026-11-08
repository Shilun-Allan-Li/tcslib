<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.RandomizedDecisionTree.majorityThree_worstCaseCost_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-Bit Majority Cost Bound

**Claim.** Every zero-error randomized decision tree computing majority on three signs has worst-case expected query cost at least $8/3$.

**Proof.** For each seed, the selected deterministic tree computes majority, so its average cost under the hard input distribution is at least $8/3$ by the deterministic majority lower bound (`FiniteDecisionTree.majorityThree_hard_averageCost_ge`). Averaging this pointwise lower bound over the seed law preserves the inequality, since expectation is monotone and the expectation of a constant is that constant. The resulting seed average is exactly the randomized tree’s average cost under the hard distribution (`RandomizedDecisionTree.averageCostUnder_eq_seedExpectation`). Finally, the average cost under any input distribution is bounded above by the worst-case input cost (`RandomizedDecisionTree.averageCostUnder_le_worstCaseCost`), giving the claimed bound.

**Key facts.** `FABL.FiniteDecisionTree.majorityThree_hard_averageCost_ge`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_mono`, `FABL.RandomizedDecisionTree.averageCostUnder_eq_seedExpectation`, `FABL.RandomizedDecisionTree.averageCostUnder_le_worstCaseCost`.
