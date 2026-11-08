<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.unflattenBinaryMatrix_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unflattening the zero vector

**Claim.** For every $n$, unflattening the zero vector of length $n^2$ over $\mathbb F_2$ gives the zero $n\times n$ matrix.

**Proof.** At each pair of indices, unflattening reads one coordinate of the zero vector. That coordinate is zero, so every entry of the resulting matrix is zero; hence it is the zero matrix.
