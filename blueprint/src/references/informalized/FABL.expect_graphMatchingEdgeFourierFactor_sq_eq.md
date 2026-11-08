<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.expect_graphMatchingEdgeFourierFactor_sq_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean Square of a Matching Fourier Factor

**Claim.** The expected squared absolute Fourier coefficient indexed by labels on the matching edges incident with a specified part equals the expected squared Fourier coefficient indexed by the image of a uniformly random map from the $k$ positions to the label set.

**Proof.** The squared factor depends only on the labels assigned to edges incident with the specified part (`FABL.graphMatchingEdgeFourierFactor_sq_dependsOn`). Therefore the expectation over labels on all matching edges equals the expectation obtained by assigning labels only to those incident edges (`FABL.expect_eq_expect_subtype_of_dependsOn`). The incident edges are in bijection with the $k$ positions of the part. Reindexing assignments along this bijection turns them into maps from the positions to the label set, preserving the uniform expectation. Under the same correspondence, each position's incident edge belongs to the incident-edge set (`FABL.graphMatchingPartEdge_mem`), so the set of labels in the Fourier index is exactly the image of that map. Finally, squaring an absolute value gives the square of the original real coefficient, yielding the claimed equality.

**Key facts.** `FABL.expect_eq_expect_subtype_of_dependsOn`, `FABL.graphMatchingEdgeFourierFactor_sq_dependsOn`, `FABL.graphMatchingPartEdge_mem`.
