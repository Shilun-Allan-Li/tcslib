<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.F₂DecisionTree.hasCNFSizeWidth_of_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CNF Bounds from a Decision Tree

**Claim.** If a decision tree computes a Boolean function after the coordinatewise binary encoding, then that function has a CNF with at most the tree's number of leaves and width at most its depth.

**Proof.** Apply the decision-tree construction of a CNF with size bounded by the number of leaves and width bounded by the depth to the Boolean function represented by the tree's evaluation (`hasCNFSizeWidth_of_decisionTree`). The computation hypothesis identifies the tree's evaluation, after binary encoding, with the given function. Rewriting along this equality transfers both bounds and the represented function to the given one.

**Key facts.** `FABL.F₂DecisionTree.hasCNFSizeWidth_of_decisionTree`.
