<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.partiteMatchingGraphOfCode_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Code-to-Matching Map

**Claim.** When $k>0$ and $qk$ is even, sending a code for a perfect matching on the $qk$ vertices, whose decoded edges join different parts, to its associated perfect matching in the complete $q$-partite graph is injective.

**Proof.** Suppose two admissible codes give the same perfect matching. Equality of the matching subtypes implies equality of their underlying subgraphs, and hence equality of the corresponding adjacency relations. The graph formed from the decoded edge list is therefore the same for both codes. The vertex list has length $qk=2((qk)/2)$ by `FABL.length_bookVertexList` and has no repetitions by `FABL.nodup_bookVertexList`. The uniqueness result for reconstructing a matching code from its edge-list graph, applied to this list, says the two codes are equal (`FABL.pairListGraph_decodePerfectMatchingCode_injective`). Thus the map is injective. The assumptions ensure the stated construction is defined; the recovery argument uses the evenness to obtain the required length and the list's distinctness.

**Key facts.** `FABL.length_bookVertexList`, `FABL.nodup_bookVertexList`, `FABL.pairListGraph_decodePerfectMatchingCode_injective`.
