<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.cfgWord_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Chunk Prefix of the Configuration Word

**Claim.** The first $W(2s+1)$ bits of the encoded configuration word are exactly the concatenation of the encoded chunks for its cells.

**Proof.** The configuration word begins with the concatenation of the cell chunks, followed by the padded input-position segment and final marker. The chunk concatenation has length $W(2s+1)$ (`length_chunksWord`). Taking exactly that many initial bits therefore returns the chunk concatenation itself.

**Key facts.** `Complexity.Codec.length_chunksWord`.
