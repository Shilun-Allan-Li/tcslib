<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.expect_sq_sub_eval_truncate_zero_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truncation Error for Sign-Valued Trees

**Claim.** For a sign-valued decision tree, the expected squared error from truncating at depth $k$ and assigning zero at truncated leaves is at most the number of leaves times $2^{-k}$.

**Proof.** First, bound the squared error at each input by the sum of indicators of paths in the tree whose lengths exceed $k$ (`sq_sub_eval_truncate_zero_le_longPathIndicatorSum`). Taking expectations preserves this inequality. The expected path-indicator sum is exactly the sum of the inverse path sizes over paths longer than $k$ (`expect_longPathIndicatorSum`). That sum is at most the number of paths times $2^{-k}$ (`sum_longPath_inversePathSize_le`). Finally, the number of paths equals the tree's leaf count (`length_paths_eq_leafCount`), yielding the required bound.

**Key facts.** `FABL.F₂DecisionTree.sq_sub_eval_truncate_zero_le_longPathIndicatorSum`, `FABL.F₂DecisionTree.expect_longPathIndicatorSum`, `FABL.F₂DecisionTree.sum_longPath_inversePathSize_le`, `FABL.F₂DecisionTree.length_paths_eq_leafCount`.
