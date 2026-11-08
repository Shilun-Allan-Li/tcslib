<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.decodedBookPartiteEdges_map_fin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoded Edges in Vertex Coordinates

**Claim.** Mapping both endpoints of every decoded book edge to their corresponding elements of $\mathrm{Fin}(qk)$ gives exactly the list obtained by decoding the code from the standard list of elements of $\mathrm{Fin}(qk)$.

**Proof.** The book vertex list is obtained by mapping the standard finite-vertex list through the inverse vertex equivalence. The decoding map commutes with mapping every vertex by a function (`decodePerfectMatchingCode_map`), so decoding this mapped list and then applying the vertex equivalence to both endpoints cancels the inverse equivalence on each vertex. The resulting list is precisely the decoding of the original standard finite-vertex list.

**Key facts.** `FABL.decodePerfectMatchingCode_map`.
