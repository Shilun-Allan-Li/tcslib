<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.sq_sub_eval_truncate_zero_le_longPathIndicatorSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truncation Error Along Long Paths

**Claim.** For a real-valued decision tree whose outputs are all $-1$ or $1$, the squared difference between its value and the value after truncating at depth $k$ with fallback zero is at most the number of matching paths longer than $k$.

**Proof.** The truncated tree’s value at the input is either the original value or the fallback zero (`FABL.F₂DecisionTree.eval_truncate_eq_eval_or_eq_fallback`). If it is the original value, the squared difference is zero, while the long-path indicator sum is nonnegative (`FABL.F₂DecisionTree.longPathIndicatorSum_nonneg`). Otherwise, the two values differ. Since the original value is either $-1$ or $1$, it is nonzero, so this case indeed represents a truncation error. A differing value guarantees a path in the tree’s path list that matches the input and has length greater than $k$ (`FABL.F₂DecisionTree.exists_long_path_of_eval_truncate_ne`). Such a path contributes one to the long-path indicator sum, so that sum is at least one (`FABL.F₂DecisionTree.one_le_longPathIndicatorSum_of_mem_of_matches`). In this case the truncated value is zero and the original value is $\pm1$, making their squared difference exactly one. This proves the bound in both cases.

**Key facts.** `FABL.F₂DecisionTree.eval_truncate_eq_eval_or_eq_fallback`, `FABL.F₂DecisionTree.longPathIndicatorSum_nonneg`, `FABL.F₂DecisionTree.exists_long_path_of_eval_truncate_ne`, `FABL.F₂DecisionTree.one_le_longPathIndicatorSum_of_mem_of_matches`.
