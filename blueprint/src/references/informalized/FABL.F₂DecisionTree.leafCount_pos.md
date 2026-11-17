<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTreeFourier.lean :: FABL.F₂DecisionTree.leafCount_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Leaf Count

**Claim.** Every decision tree on a finite set of coordinates has at least one leaf.

**Proof.** Proceed by induction on the tree. A leaf has leaf count $1$, which is positive. A query node has two child trees; by induction each child has positive leaf count. The node's leaf count is their sum, hence is positive.
