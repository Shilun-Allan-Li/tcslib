<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.cfgWord_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Bit of the Configuration Word

**Claim.** The bit at index $W(2s+1)+w_P(|x|)$ of the encoded configuration word is true.

**Proof.** First, the concatenation of the chunks and padded input-position segment has length $W(2s+1)+w_P(|x|)$. The chunk length is the number of chunks times their width (`length_chunksWord`), while the padded segment has length $w_P(|x|)`: the input position is at most $|x|+1$, so its bit list fits within that width (`length_bits_pos_le`), and padding then gives exactly the requested width (`length_padBits`). The configuration word appends a single `true` after this concatenation. Hence the specified index is precisely the position of that final bit.

**Key facts.** `Complexity.Codec.length_chunksWord`, `Complexity.Codec.length_bits_pos_le`, `Complexity.Codec.length_padBits`.
