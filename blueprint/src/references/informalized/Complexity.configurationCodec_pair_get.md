<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationCodec_pair_get -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paired Configuration Code Lookup

**Claim.** For two inputs of length $n$, a chosen side and coordinate in the paired encoding retrieve the corresponding bit of that configuration's code row.

**Proof.** The coefficient bound ensures every coordinate of the finite set of row bits lies within the allocated code length (`codecBit_card_le`). Split according to which side is selected. On the first side, the coordinate lies in the first code block; on the second, it lies in the second block after the first block's length is subtracted. The two blocks have the stated common length (`configurationCodec_length`), so list lookup reduces in each case to lookup in the selected configuration's code word. At the index associated with a row-bit coordinate, that word returns precisely the row bit (`codecWord_get`).

**Key facts.** `Complexity.codecBit_card_le`, `Complexity.configurationCodec_length`, `Complexity.codecWord_get`.
