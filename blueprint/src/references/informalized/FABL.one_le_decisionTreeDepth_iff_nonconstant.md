<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.one_le_decisionTreeDepth_iff_nonconstant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision tree depth detects nonconstancy

**Claim.** A Boolean function has minimum decision tree depth at least one exactly when it takes different values on some pair of inputs.

**Proof.** Suppose first that the function is not constant. Take a decision tree computing it whose depth realizes the minimum (`exists_computingTree_depth_eq_decisionTreeDepth`). If its depth were zero, every input would receive the same value by the depth-zero evaluation property (`eval_eq_of_depth_eq_zero`). Since the tree computes the function (`computes_iff`), this would make the function constant, a contradiction. Conversely, if the function were constant, the leaf storing its value at the zero input would compute it, by the pointwise characterization of computation (`computes_iff`). The minimum depth is no greater than the depth of any computing tree (`decisionTreeDepth_le_of_computes`), so it would be zero. Hence depth at least one rules out constancy, which is equivalent to the existence of inputs with different values.

**Key facts.** `FABL.F₂DecisionTree.exists_computingTree_depth_eq_decisionTreeDepth`, `FABL.F₂DecisionTree.eval_eq_of_depth_eq_zero`, `FABL.F₂DecisionTree.computes_iff`, `FABL.F₂DecisionTree.decisionTreeDepth_le_of_computes`.
