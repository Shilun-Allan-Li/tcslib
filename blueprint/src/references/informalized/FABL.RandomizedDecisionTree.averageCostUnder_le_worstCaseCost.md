<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.RandomizedDecisionTree.averageCostUnder_le_worstCaseCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average Cost Bounded by Worst-Case Cost

**Claim.** For any randomized decision tree and input distribution, its average query cost is at most its worst-case query cost over all inputs.

**Proof.** For each input, the input cost is at most the worst-case cost (`RandomizedDecisionTree.inputCost_le_worstCaseCost`). Averaging this pointwise inequality over the input distribution preserves the inequality, by monotonicity of finite probability expectation (`pmfExpectation_mono`). The expectation of the constant worst-case cost is that same constant (`pmfExpectation_const`), proving the bound.

**Key facts.** `FABL.RandomizedDecisionTree.inputCost_le_worstCaseCost`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_const`.
