<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.exists_computingTree_with_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of a Computing Tree with Depth

**Claim.** Every function on the Boolean cube is computed by a decision tree, and that tree has some natural-number depth.

**Proof.** Take the complete decision tree for the function. The completeness theorem (`FABL.F₂DecisionTree.completeTree_computes`) states that this tree computes the function. Its depth is a natural number, so choosing that depth and the complete tree gives the asserted witness.

**Key facts.** `FABL.F₂DecisionTree.completeTree_computes`.
