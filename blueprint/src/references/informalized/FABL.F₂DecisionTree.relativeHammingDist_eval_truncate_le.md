<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.relativeHammingDist_eval_truncate_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision Tree Truncation Error Bound

**Claim.** For a decision tree $T$, fallback value $a$, and truncation depth $k$, the fraction of inputs on which $T$ differs from its truncation is at most $L(T)2^{-k}$, where $L(T)$ is the number of leaves.

**Proof.** First express the fraction of inputs on which the two trees disagree as the uniform probability of disagreement; this is the relative-Hamming-distance identity (`uniformProbability_ne_eq_relativeHammingDist`). For each input, if the trees disagree, there is a generated path that matches the input and has length greater than $k$ (`exists_long_path_of_eval_truncate_ne`). Such a path contributes at least $1$ to the sum of long-path indicators, so the disagreement indicator is bounded by that sum. When the trees agree, the disagreement indicator is zero and is bounded by the sum because the sum is nonnegative (`longPathIndicatorSum_nonneg`). Taking uniform expectations preserves the inequality. The expectation of the long-path indicator sum is the sum, over generated paths, of their inverse path sizes when their lengths exceed $k$ (`expect_longPathIndicatorSum`). This sum is at most the number of paths times $2^{-k}$ (`sum_longPath_inversePathSize_le`). Finally, the number of generated paths equals the number of leaves (`length_paths_eq_leafCount`), giving the claimed bound.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`, `FABL.F₂DecisionTree.exists_long_path_of_eval_truncate_ne`, `FABL.F₂DecisionTree.one_le_longPathIndicatorSum_of_mem_of_matches`, `FABL.F₂DecisionTree.longPathIndicatorSum_nonneg`, `FABL.F₂DecisionTree.expect_longPathIndicatorSum`, `FABL.F₂DecisionTree.sum_longPath_inversePathSize_le`, `FABL.F₂DecisionTree.length_paths_eq_leafCount`.
