<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.decode_finVertexList_map_val -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoded finite vertex lists

**Claim.** Mapping the decoded pairs from the list of all elements of $\mathrm{Fin}(N)$ to their natural-number values gives the same result as decoding directly from $[0,1,\ldots,N-1]$.

**Proof.** Apply the relabelling identity for decoding (`FABL.decodePerfectMatchingCode_map`) with the map taking each finite index to its natural-number value. It identifies the mapped decoded-pair list with decoding from the mapped vertex list. The mapped list of all elements of $\mathrm{Fin}(N)$ is exactly the natural-number range list (`FABL.map_val_finVertexList`), giving the result.

**Key facts.** `FABL.decodePerfectMatchingCode_map`, `FABL.map_val_finVertexList`.
