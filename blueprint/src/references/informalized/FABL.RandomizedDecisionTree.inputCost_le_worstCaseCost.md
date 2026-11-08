<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.inputCost_le_worstCaseCost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Cost and Worst-Case Cost

**Claim.** For every input, the expected query count is at most the maximum expected query count over all inputs.

**Proof.** The worst-case cost is the supremum of the input cost over the finite input space. The supremum is at least the value at any particular input, which gives the result.
