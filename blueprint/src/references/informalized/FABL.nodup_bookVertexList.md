<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.nodup_bookVertexList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Book Vertices

**Claim.** For any $q$ and $k$, the list of vertices in the complete $q$-partite indexing set with $k$ vertices in each part contains no repetitions.

**Proof.** The list is obtained by mapping the list of all elements of $\mathrm{Fin}(qk)$ through the inverse of the vertex-to-index equivalence. The original list has no repetitions (`nodup_finVertexList`), and an injective map preserves that property. The inverse equivalence is injective, so the book vertex list has no repetitions.

**Key facts.** `FABL.nodup_finVertexList`.
