<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.computes_eq_pathExpansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision tree path expansion

**Claim.** If a real-valued decision tree computes a function on the binary cube, then that function is the sum over its paths of each path's output times the indicator of the inputs matching that path.

**Proof.** The computing hypothesis identifies the function with the tree's evaluation pointwise. The path expansion identity for tree evaluation (`eval_eq_pathExpansion`) identifies that evaluation with the sum of the path outputs weighted by their matching-input indicators. Combining these equalities gives the claimed formula.

**Key facts.** `FABL.F₂DecisionTree.eval_eq_pathExpansion`.
