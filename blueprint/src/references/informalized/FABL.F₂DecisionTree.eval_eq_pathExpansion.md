<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.eval_eq_pathExpansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation as a Path Expansion

**Claim.** For every input, evaluating a real-valued decision tree equals the sum over its paths of each path's output multiplied by the indicator of inputs matching that path.

**Proof.** Apply the established path-indicator expansion identity (`FABL.F₂DecisionTree.eval_eq_sum_pathIndicators_function`), which states that the tree's evaluation is the function whose value at each input is precisely the sum of path outputs weighted by their path indicators. This is the definition of the stated path expansion.

**Key facts.** `FABL.F₂DecisionTree.eval_eq_sum_pathIndicators_function`.
