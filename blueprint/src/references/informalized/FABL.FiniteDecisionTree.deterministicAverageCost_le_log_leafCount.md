<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.FiniteDecisionTree.deterministicAverageCost_le_log_leafCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average cost and leaf count

**Claim.** For a sign-alphabet decision tree, its average number of queries under uniform independent inputs is at most the base-$2$ logarithm of its number of leaves.

**Proof.** The proof first identifies the deterministic average query cost with the auxiliary average cost for the same tree and distribution (FiniteDecisionTree.auxiliaryAverageCost_complete). It then applies the bound that the auxiliary average cost under the uniform sign distribution is at most the base-$2$ logarithm of the leaf count (FiniteDecisionTree.auxiliaryAverageCost_uniform_le_log_leafCount). Combining these gives the stated inequality.

**Key facts.** `FABL.FiniteDecisionTree.auxiliaryAverageCost_complete`, `FABL.FiniteDecisionTree.auxiliaryAverageCost_uniform_le_log_leafCount`.
