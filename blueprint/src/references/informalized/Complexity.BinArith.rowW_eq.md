<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.rowW_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded Row Elimination

**Claim.** Applying the encoded row transformation to the encodings of $p$, $\mathrm{inv}$, the tail of $\mathrm{piv}$, and $\mathrm{row}$ produces the encoding of the row-elimination result, entry by entry.

**Proof.** The projections of each nested pair encoding recover its original components. The encoded row's first projection is the binary representation of its head entry (with zero for an empty row), and its second projection encodes the tail. The theorem describing the encoded zip operation then reduces the outer computation to pairing corresponding decoded entries from the row and pivot tails, applying the entry transformation to each pair, and encoding the resulting list. The entry transformation theorem identifies each output as the binary representation of $(r+p-(\mathrm{row}_0\,\mathrm{inv}\bmod p)y\bmod p)$. Decoding an encoded row recovers the list of binary representations of its entries, so this positionwise list is exactly the encoding of the stated row-elimination operation, including its shorter-list behavior.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.BinArith.pairFstD_encRow`, `Complexity.BinArith.pairSndD_encRow`, `Complexity.BinArith.zipWithW_pairEncode`, `Complexity.BinArith.decWords_encRow`, `Complexity.LogProg.bitsVal_bits`, `Complexity.BinArith.entryW_eq`.
