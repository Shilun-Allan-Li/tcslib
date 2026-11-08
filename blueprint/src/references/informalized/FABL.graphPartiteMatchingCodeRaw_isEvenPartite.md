<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphPartiteMatchingCodeRaw_isEvenPartite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partite Matching Code Property

**Claim.** For $k>0$, the code assigned to a perfect matching in the complete $2r$-partite graph with $k$ vertices in each part decodes so that every paired pair has endpoints in different parts, as detected by their quotients upon division by $k$.

**Proof.** To verify the defining condition, consider any decoded edge $(a,b)$. The decoded-edge correspondence gives bounds $a,b<2rk$ and shows that the corresponding vertices are adjacent in the perfect matching graph of the code (`decodedRangeEdge_perfectMatchingGraph_adj`). Since the code is obtained by applying the inverse matching-code equivalence to the relabeled partite matching, applying the forward equivalence recovers that relabeled matching. Thus the vertices corresponding to $a$ and $b$ are adjacent in the original partite matching. Adjacency in a complete multipartite graph forces the vertices to lie in different parts. If $a/k=b/k$, the quotient formula for the vertex relabeling (`bookVertexEvenFinEquiv_val_div`) identifies both part indices with this same quotient, contradicting that they lie in different parts. Hence $a/k\ne b/k$, for every decoded edge.

**Key facts.** `FABL.decodedRangeEdge_perfectMatchingGraph_adj`, `FABL.bookVertexEvenFinEquiv_val_div`.
