<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.F₂DecisionTree.depth_mapOutputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth under output mapping

**Claim.** Applying any map to the outputs at the leaves of a decision tree leaves its depth unchanged.

**Proof.** Proceed by induction on the tree. Mapping the output of a leaf leaves a leaf, of depth zero. For a query, the mapped tree has the same query and its two child trees are the mapped versions of the original children. The induction hypotheses give equality of the depths of each corresponding pair of children. Thus their maximum depths agree, and adding one for the query gives equal tree depths.
