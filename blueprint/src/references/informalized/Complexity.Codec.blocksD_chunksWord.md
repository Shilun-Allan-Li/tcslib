<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Step.lean :: Complexity.Codec.blocksD_chunksWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding Concatenated Chunks

**Claim.** Decoding the first $m$ blocks of the concatenation of the first $m$ encoded cell values gives, in order, the values $f(0),\ldots,f(m-1)$, each as a successfully decoded cell value.

**Proof.** Compare the two lists entry by entry. For each index $j<m$, the block identity (`block_chunksWord`) identifies block $j$ of the concatenation with the encoding of $f(j)$. Decoding that encoding returns $f(j)$ successfully (`decChunk_encChunk`). Thus every corresponding entry agrees, and the decoded list is precisely the stated list of successful decodings.

**Key facts.** `Complexity.Codec.block_chunksWord`, `Complexity.Codec.decChunk_encChunk`.
