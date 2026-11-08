<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.block_chunksWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blocks of a Concatenated Chunk Word

**Claim.** If $j<m$, then block $j$ of the concatenation of the first $m$ encoded cell values is the encoding of $f(j)$.

**Proof.** The concatenated word is a flattening of $m$ chunks, each of width $W(N)$. The flattening block identity (`take_drop_flatten`) says that dropping $j$ whole blocks and taking one block recovers the $j$th chunk, provided all chunks have that width and $j<m$. Each encoded chunk has width $W(N)$ by construction, so the recovered chunk is the encoding of $f(j)$.

**Key facts.** `Complexity.Codec.take_drop_flatten`.
