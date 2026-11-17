<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.flattenBinaryMatrix_unflattenBinaryMatrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flattening After Unflattening

**Claim.** Flattening the matrix obtained by unflattening a vector returns the original vector.

**Proof.** It suffices to compare the two vectors at an arbitrary coordinate $k$. Unflattening reads the original vector at the image of the pair corresponding to $k$; flattening then applies the inverse pairing map to recover that pair. Since an equivalence followed by its inverse is the identity, the resulting coordinate is the original value at $k$.
