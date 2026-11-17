<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.f₂DotProduct_flattenBinaryMatrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing Flattened Binary Matrices

**Claim.** The dot product of the flattened matrices A and B equals the sum over all pairs of indices of AᵢⱼBᵢⱼ.

**Proof.** Expand the dot product as a sum indexed by flattened coordinates. The coordinate equivalence between indices of the flattened vector and pairs (i,j) is a bijection, so reindexing the finite sum gives the sum over all pairs of matrix indices. Splitting this product-indexed sum into its two iterated sums yields the stated matrix pairing.
