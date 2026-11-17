<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.decodedBookPartiteEdge_parts_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoded Edges Join Distinct Parts

**Claim.** Every edge decoded from a partite perfect-matching code has endpoints in different parts.

**Proof.** Map the decoded book edge through the vertex equivalence to an edge on `Fin (qk)`. The edge-list mapping identity (`decodedBookPartiteEdges_map_fin`) and the identity relating decoding on `Fin` vertices to decoding on their natural-number values (`decode_finVertexList_map_val`) show that this pair occurs in the natural-number decoding list. The code’s partite condition therefore says that the two endpoint values, each divided by $k$, are different. The quotient formula for the vertex equivalence (`bookVertexFinEquiv_val_div`) identifies these quotients with the values of the endpoints’ part coordinates. Thus those coordinates cannot be equal.

**Key facts.** `FABL.decodedBookPartiteEdges_map_fin`, `FABL.decode_finVertexList_map_val`, `FABL.bookVertexFinEquiv_val_div`.
