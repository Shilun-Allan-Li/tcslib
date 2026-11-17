<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.decChunk_encChunk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Chunk Decoding Recovers Encoding

**Claim.** For every machine $N$ and cell value $v$, decoding the encoded chunk of $v$ returns $v$.

**Proof.** By definition, decoding returns a chosen cell value whenever the input chunk is the encoding of some cell value. For the chunk encoded from $v$, such a witness exists, namely $v$ itself. The decoder therefore returns its chosen witness. The witness and $v$ have the same encoding, so injectivity of the chunk encoding (`encChunk_injective`) makes them equal. Thus decoding returns $v$.

**Key facts.** `Complexity.Codec.encChunk_injective`.
