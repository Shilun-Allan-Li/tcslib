<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.exists_computingTree_depth_eq_decisionTreeDepth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Tree Attaining Minimum Depth

**Claim.** For every function on the Boolean cube, there is a decision tree computing it whose depth equals its decision tree depth.

**Proof.** By the existence result for computing trees with a specified depth (`FABL.F₂DecisionTree.exists_computingTree_with_depth`), the set of depths of computing trees is nonempty. The decision tree depth is defined as the least such natural number. The defining property of this least number therefore supplies a computing tree whose depth is exactly the decision tree depth.

**Key facts.** `FABL.F₂DecisionTree.exists_computingTree_with_depth`.
