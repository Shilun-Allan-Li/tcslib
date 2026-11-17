<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.getD_cfgWord_chunk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration word chunk lookup

**Claim.** At every chunk index $j<2s+1$ and bit position $t<W(N)$, the configuration word's bit at position $W(N)j+t$ is bit $t$ of the encoding of the cell at index $j$ relative to shift $s$.

**Proof.** First, the bounds on $j$ and $t$ imply $W(N)j+t<W(N)(2s+1)$. The configuration word begins with the concatenation of its $2s+1$ encoded cell chunks, whose total length is $W(N)(2s+1)$ (`length_chunksWord`). Therefore this position lies before the appended input-position padding and final marker, so its lookup in the full word agrees with its lookup in the concatenated chunks. Each chunk has length $W(N)$; the fixed-width flattening identity (`getD_flatten_block`) identifies position $W(N)j+t$ in that concatenation with position $t$ in chunk $j$. The chunk is the encoding of the cell at index $j$, and its lookup equals the corresponding encoded bit (`getD_encChunk`).

**Key facts.** `Complexity.Codec.length_chunksWord`, `Complexity.Codec.getD_flatten_block`, `Complexity.Codec.getD_encChunk`.
