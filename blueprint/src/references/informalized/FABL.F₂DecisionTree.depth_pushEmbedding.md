<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.F₂DecisionTree.depth_pushEmbedding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth under pushing forward by an embedding

**Claim.** Pushing a decision tree forward along a coordinate embedding, with the stated availability condition, preserves its depth.

**Proof.** Proceed by induction on the tree, allowing the target coordinate set to vary. A leaf remains a leaf. At a query, pushing forward retains a query at the embedded coordinate, and the two children are the pushforwards of the original children. By the induction hypotheses, each pushed-forward child has the same depth as its original. Their maximum depths therefore agree, and adding one for the query proves equality of the whole-tree depths.
