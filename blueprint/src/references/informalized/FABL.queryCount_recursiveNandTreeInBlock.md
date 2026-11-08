<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.queryCount_recursiveNandTreeInBlock -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query count under NAND block reindexing

**Claim.** The query count of the reindexed tree on the larger cube equals the query count of the original tree on the restriction to block $i$.

**Proof.** Reindexing sends each coordinate queried by the original tree to its embedded coordinate in block $i$. Thus the reindexed query trace has the same length as the original tree's trace evaluated on the larger input pulled back along that embedding (`FiniteDecisionTree.queryTrace_reindex_length`). By definition, this pulled-back input is the restriction of $x$ to block $i$, so their query counts agree.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_reindex_length`.
