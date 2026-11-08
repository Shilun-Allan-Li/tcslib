<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.exists_computingTree_leafCount_eq_decisionTreeSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Tree Attaining Minimum Size

**Claim.** For every function on the Boolean cube, there is a decision tree computing it whose leaf count equals its decision tree size.

**Proof.** The existence result for computing trees with a specified leaf count (`FABL.F₂DecisionTree.exists_computingTree_with_size`) ensures that some computing tree exists, so the set of leaf counts of computing trees is nonempty. The decision tree size is the least such natural number. By the defining property of this least number, a computing tree has leaf count equal to the decision tree size.

**Key facts.** `FABL.F₂DecisionTree.exists_computingTree_with_size`.
