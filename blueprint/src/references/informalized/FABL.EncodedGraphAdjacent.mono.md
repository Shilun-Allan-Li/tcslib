<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GraphPropertyExamples.lean :: FABL.EncodedGraphAdjacent.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Encoded Adjacency

**Claim.** If every edge present in one encoded graph is present in another, then every pair of distinct vertices adjacent in the first graph is adjacent in the second.

**Proof.** Unpack adjacency in the first graph: the vertices are distinct, and there is a two-element edge containing both whose encoding in the first graph is true. Edge inclusion makes the encoding of that same edge true in the second graph. The distinctness and incidence conditions are unchanged, so the vertices are adjacent there as well.
