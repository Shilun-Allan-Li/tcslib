<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.pairFstD_encMat_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First projection of an encoded matrix

**Claim.** For a row $r$ and a list of rows $R$, the first projection of the encoding of the matrix with first row $r$ and remaining rows $R$ is the encoding of $r$.

**Proof.** The matrix encoding first maps each row to its row encoding, then encodes the resulting list of bit strings. The first projection of such an encoded list recovers its first bit string. For the matrix $r::R$, that first bit string is the row encoding of $r$, as required.
