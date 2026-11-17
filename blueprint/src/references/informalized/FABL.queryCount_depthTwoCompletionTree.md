<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.queryCount_depthTwoCompletionTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-Two Completion Query Count

**Claim.** The depth-two completion tree queries one coordinate when the known sign agrees with the selected block's value at the cyclic second coordinate, and two coordinates otherwise.

**Proof.** First transfer the query-trace length through the block embedding: reindexing a decision tree changes the coordinate names in its trace but preserves the number of queries (`FiniteDecisionTree.queryTrace_reindex_length`). The embedded input values agree with the corresponding coordinates of the selected block by the definition of the embedding and recursive input block. It remains to inspect the three possible seeds. For each seed, the completion tree first queries the cyclic second coordinate. If that observed sign equals the known sign, the next node is a leaf, so the trace has length one. If they differ, the tree queries the cyclic third coordinate and then stops, giving length two. These are precisely the two cases in the stated model cost.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_reindex_length`.
