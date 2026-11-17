<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.queryTrace_reindex_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trace Length Under Reindexing

**Claim.** If $e$ injectively maps the $m$ coordinates into the $n$ coordinates, reindexing a tree along $e$ preserves the length of its trace, with the original tree evaluated on $i\mapsto x(e(i))$.

**Proof.** Proceed by induction on the tree. A leaf has trace length zero on both sides. At a query node, reindexing replaces the queried coordinate by its image under $e$ and reindexes the selected child; the intervening cast of available sets does not change the child trace (`queryTrace_castAvailable`). Each trace therefore has one initial query, and the induction hypothesis identifies the lengths of the two remaining traces for the selected child. Adding one to both lengths gives the result.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_castAvailable`.
