<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.length_paths_eq_leafCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Path and Leaf Counts

**Claim.** For every decision tree on a finite set of coordinates, the number of paths in its path list equals its number of leaves.

**Proof.** Proceed by induction on the tree. A leaf contributes one path and has leaf count $1$, so the two counts agree. At a query node, the path list is formed by joining the path lists of its two children, while the leaf count is the sum of the children’s leaf counts. By induction the lengths of the two child path lists equal their respective leaf counts; adding these equalities proves the result for the query node.
