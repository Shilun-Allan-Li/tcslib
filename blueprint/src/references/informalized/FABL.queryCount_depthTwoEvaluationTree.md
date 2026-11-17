<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.queryCount_depthTwoEvaluationTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-Two Evaluation Query Count

**Claim.** The depth-two evaluation tree queries two coordinates when the selected block's values at the cyclic first and second coordinates agree, and three otherwise.

**Proof.** Reindexing the tree into the chosen block preserves the length of its query trace (`FiniteDecisionTree.queryTrace_reindex_length`), and each embedded coordinate reads the corresponding value in that block. For each of the three seeds, the cyclic tree first queries the first coordinate and then the second. If their observed values agree, it stops, so the trace has length two. If they differ, it queries the third coordinate before stopping, so the trace has length three. This is exactly the two-case definition of the model cost.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_reindex_length`.
