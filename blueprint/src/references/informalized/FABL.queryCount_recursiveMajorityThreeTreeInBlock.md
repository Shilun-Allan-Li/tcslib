<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.queryCount_recursiveMajorityThreeTreeInBlock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query count under block reindexing

**Claim.** The query count of the reindexed tree on the larger cube equals the query count of the original tree on the restriction to block $i$.

**Proof.** Reindexing replaces each queried coordinate of the original tree by its image in block $i$. The query trace of a reindexed tree therefore has the same length as the original query trace evaluated on the input whose coordinate at $j$ is the larger input's value at the embedded coordinate. By the definition of the block restriction, this input is exactly the restriction of $x$ to block $i$. Taking trace lengths gives the claimed equality (the reindexing trace-length identity, `FiniteDecisionTree.queryTrace_reindex_length`).

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_reindex_length`.
