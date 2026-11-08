<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.encChunk_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Chunk Encoding

**Claim.** For every finite nondeterministic Turing machine $N$, if two cell values have the same encoded chunk, then the cell values are equal.

**Proof.** Suppose two cell values have the same encoded chunk. Equality of the chunks implies equality of their bits at every valid position, by reading each chunk at that position (`getD_encChunk`). First consider the head slot. Its positions encode, by distinct indicator bits, the numerical code of an optional head. Equality of those bits forces the two optional heads to agree: if one is present, its code occurs in the corresponding position, and equality of the codes implies equality of the heads (`hdNum_injective`); if one is absent, the other cannot be present. Thus the head slots coincide. For each tape, inspect the three positions assigned to it. By the tape-slot decoding rule (`chunkBit_tape`), these bits record whether the symbol is present, the Boolean symbol when present, and whether the head is at that tape cell. Equality of these three bits forces the tape-cell data to agree, including the option symbol. Since this holds for every tape, the tape functions coincide as well, and hence the cell values are equal.

**Key facts.** `Complexity.Codec.getD_encChunk`, `Complexity.Codec.hdNum_lt`, `Complexity.Codec.hdNum_injective`, `Complexity.Codec.chunkBit_tape`.
