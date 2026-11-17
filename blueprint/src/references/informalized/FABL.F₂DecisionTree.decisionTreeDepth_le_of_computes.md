<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.decisionTreeDepth_le_of_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minimum depth bounds every computing tree

**Claim.** The minimum decision tree depth of a function is at most the depth of any decision tree computing it.

**Proof.** There exists a computing tree whose depth is the minimum decision tree depth (`exists_computingTree_with_depth`), so the minimum is well-defined. The given tree is also a witness to the existence of a computing tree at its own depth. By the defining minimality of the chosen natural number, the minimum depth is no greater than that depth.

**Key facts.** `FABL.F₂DecisionTree.exists_computingTree_with_depth`.
