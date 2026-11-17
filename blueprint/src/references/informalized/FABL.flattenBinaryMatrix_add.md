<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.flattenBinaryMatrix_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flattening Preserves Matrix Addition

**Claim.** Flattening the sum of two matrices over the field with two elements gives the sum of their flattened vectors.

**Proof.** At each vector coordinate, flattening reads the matrix entry indexed by the pair corresponding to that coordinate. Matrix addition is defined entrywise, so the selected entry of the sum is the sum of the two selected entries. Thus the flattened functions agree at every coordinate.
