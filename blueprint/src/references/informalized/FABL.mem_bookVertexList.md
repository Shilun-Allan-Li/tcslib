<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.mem_bookVertexList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Book Vertex List Membership

**Claim.** For natural numbers q,k, every vertex (a,b), with a ∈ {0,…,q−1} and b ∈ {0,…,k−1}, belongs to the book vertex list.

**Proof.** Map the vertex through the book-vertex equivalence to an element of Fin(qk). Every element of Fin(qk) occurs in the list of all such finite indices (FABL.mem_finVertexList). Mapping that index back by the inverse equivalence gives the original vertex, so it appears in the book vertex list.

**Key facts.** `FABL.mem_finVertexList`.
