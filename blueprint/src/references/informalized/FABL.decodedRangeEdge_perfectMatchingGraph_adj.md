<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.decodedRangeEdge_perfectMatchingGraph_adj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoded Edges Are Matching Graph Edges

**Claim.** If $(a,b)$ occurs in the decoding from $[0,1,\ldots,2m-1]$, then both values are less than $2m$, and their represented vertices are adjacent in the perfect-matching graph determined by the code.

**Proof.** First, the flattened list of endpoints of all decoded edges is a permutation of the input vertex list (`flattenPairList_decodePerfectMatchingCode_perm`). Each endpoint of the given edge occurs in that flattened list, so each occurs in the range list and hence is less than $2m$. Represent them by the corresponding elements of $\mathrm{Fin}(2m)$. The decoding identity under taking vertex values (`decode_finVertexList_map_val`) shows that this represented pair occurs in the decoding from the standard finite-vertex list. The flattened decoded list has no repeated vertices (`flattenPairList_decodePerfectMatchingCode_nodup`), using that the standard finite-vertex list has no repetitions (`nodup_finVertexList`). In particular, the two endpoints of this pair are distinct. By the adjacency characterization for a graph built from an edge list (`pairListGraph_adj_iff`), an edge in the list with distinct endpoints gives adjacency in the graph of decoded pairs. That graph is the matching graph used to define the perfect-matching graph of the code.

**Key facts.** `FABL.flattenPairList_decodePerfectMatchingCode_perm`, `FABL.nodup_finVertexList`, `FABL.decode_finVertexList_map_val`, `FABL.flattenPairList_decodePerfectMatchingCode_nodup`, `FABL.pairListGraph_adj_iff`.
