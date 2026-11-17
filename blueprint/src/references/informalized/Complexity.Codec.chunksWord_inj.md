<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.chunksWord_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Chunk Encoding

**Claim.** If the words formed by concatenating the first $m$ encoded cell values of $f$ and $g$ are equal, then $f(j)=g(j)$ for every $j<m$.

**Proof.** Each encoded cell has the fixed length $W$. Thus, in either concatenated word, the $j$th chunk is recovered by dropping the first $Wj$ bits and taking the next $W$ bits; the fixed-width flattening lemma justifies this recovery (`take_drop_flatten`). Equality of the full words therefore gives equality of the two $j$th chunks. Since the encoding of an individual cell value is injective (`encChunk_injective`), the cell values themselves are equal.

**Key facts.** `Complexity.Codec.take_drop_flatten`, `Complexity.Codec.encChunk_injective`.
