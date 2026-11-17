<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.F₂DecisionTree.depth_complementInputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth under input complementation

**Claim.** Complementing the input bits of a binary decision tree leaves its depth unchanged.

**Proof.** Proceed by induction on the tree. A leaf remains a leaf, so both depths are zero. At a query, complementing the inputs swaps the roles of the zero-child and one-child trees. By the induction hypotheses, each child has the same depth as its corresponding original child. Since the maximum of two numbers is unchanged when their order is swapped, the maximum child depth, and hence the depth after adding one for the query, is unchanged.
