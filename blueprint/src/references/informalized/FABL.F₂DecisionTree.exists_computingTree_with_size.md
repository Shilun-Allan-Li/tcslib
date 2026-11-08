<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.exists_computingTree_with_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of a Computing Tree with Leaf Count

**Claim.** Every function on the Boolean cube is computed by a decision tree, and that tree has some natural-number leaf count.

**Proof.** Take the complete decision tree for the function. The completeness theorem (`FABL.F₂DecisionTree.completeTree_computes`) says it computes the function. Its leaf count is a natural number, so choosing that count and the complete tree gives the required witness.

**Key facts.** `FABL.F₂DecisionTree.completeTree_computes`.
