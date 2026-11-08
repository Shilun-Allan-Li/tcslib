<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.decWords_encMat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an encoded matrix

**Claim.** For a list $R$ of rows of natural numbers, decoding the matrix encoding yields the list of encoded rows, namely the images of the rows under `encRow`.

**Proof.** By definition, the matrix encoding is the concatenation of the pair encodings of the row encodings, each with empty second component. Unfolding this encoding and the recursive decoder, each successive pair encoding decodes to its row encoding and leaves the remaining concatenation of row encodings to decode. The resulting list is exactly the list of encoded rows.
