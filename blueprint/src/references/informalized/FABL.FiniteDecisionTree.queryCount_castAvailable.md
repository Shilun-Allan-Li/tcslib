<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.queryCount_castAvailable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query count under a change of available set

**Claim.** If two available-coordinate sets are equal, casting a tree from one set to the other leaves its query count on every input unchanged.

**Proof.** The query count is the length of the query trace. Casting the tree along an equality of available sets leaves that trace unchanged (\texttt{queryTrace_castAvailable}); taking lengths gives the stated equality.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_castAvailable`.
