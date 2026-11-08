<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.pairSndD_encMat_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering the Remaining Matrix Rows

**Claim.** For a row $r$ of natural numbers and a list $R$ of such rows, the total second projection of the encoding of the matrix whose first row is $r$ and whose remaining rows are $R$ equals the encoding of $R$.

**Proof.** By definition, the matrix encoding concatenates the pair encodings of its rows. Its first pair encoding has the encoded first row as its first component and an empty second component; the remaining concatenated data follows the pair delimiter. Decoding this outer pair therefore returns precisely the concatenation of the encodings of the rows in $R$, which is the encoding of $R$.
