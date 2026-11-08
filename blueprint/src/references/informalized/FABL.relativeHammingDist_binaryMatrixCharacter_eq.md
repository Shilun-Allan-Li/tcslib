<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.relativeHammingDist_binaryMatrixCharacter_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance Between Binary Matrix Characters

**Claim.** For square matrices $A$ and $B$ over the field with two elements, the relative Hamming distance between their binary matrix characters is $0$ if $A=B$ and $1/2$ otherwise.

**Proof.** Reindex the input matrices as vectors of length $n^2$; this preserves relative Hamming distance (`FABL.relativeHammingDist_unflattenBinaryMatrix`). Under this reindexing, each matrix character becomes the dot-product character associated to the flattened matrix (`FABL.binaryMatrixCharacter_unflattenBinaryMatrix`). The distance between two such dot-product characters is $0$ when their coefficient vectors agree and $1/2$ otherwise (`FABL.relativeHammingDist_f₂DotProduct_eq`). If $A=B$, their flattened vectors agree. Conversely, equality of the flattened vectors implies $A=B$, since flattening is injective through the matrix-cube equivalence. Thus the dot-product distance formula is exactly the claimed matrix formula.

**Key facts.** `FABL.relativeHammingDist_unflattenBinaryMatrix`, `FABL.binaryMatrixCharacter_unflattenBinaryMatrix`, `FABL.relativeHammingDist_f₂DotProduct_eq`.
