<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.unflattenBinaryMatrix_flattenBinaryMatrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unflattening a flattened matrix

**Claim.** For every $n\times n$ matrix $A$ over $\mathbb F_2$, unflattening its associated vector recovers $A$.

**Proof.** Compare the two matrices at arbitrary indices $i,j$. Flattening records the entry of $A$ at the pair corresponding to the vector coordinate, and unflattening reads that same coordinate using the inverse indexing correspondence. The resulting entry is therefore $A_{ij}$. Since the entries agree at every pair of indices, the matrices are equal.
