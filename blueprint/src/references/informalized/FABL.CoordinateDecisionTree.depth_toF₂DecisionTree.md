<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordinateDecisionTree.depth_toF₂DecisionTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Is Preserved Under Conversion

**Claim.** For a coordinate decision tree well formed with respect to an available coordinate set, converting it to a tree that tracks available coordinates preserves its depth.

**Proof.** Induct on the tree. A leaf converts to a leaf, so both depths are zero. At a query, well-formedness supplies the condition needed to convert each child after removing the queried coordinate. By the induction hypotheses, each converted child has the same depth as its original child. Both trees therefore take the maximum of the same two child depths and add one, so their depths agree.
