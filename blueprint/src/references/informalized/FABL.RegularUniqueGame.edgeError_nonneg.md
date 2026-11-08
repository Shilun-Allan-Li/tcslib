<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.edgeError_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Edge error is nonnegative

**Claim.** The expected fraction of violated constraints under a labeling, averaged over vertices and their neighbors, is nonnegative.

**Proof.** For each vertex, the local edge error is nonnegative (`FABL.RegularUniqueGame.localEdgeError_nonneg`). The expectation of a pointwise nonnegative function over the finite vertex set is nonnegative, so averaging these local errors gives a nonnegative edge error.

**Key facts.** `FABL.RegularUniqueGame.localEdgeError_nonneg`.
