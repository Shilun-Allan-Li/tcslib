<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.cfgWord_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Position Segment

**Claim.** After dropping the first $W(2s+1)$ bits and taking the next $w_P(|x|)$ bits, the configuration word yields exactly the padded bit representation of the input-head position.

**Proof.** The configuration word is the concatenation of the chunk word, the padded input-position bits, and the final marker. The chunk word has length exactly $W(2s+1)$ (`length_chunksWord`), so dropping that many bits leaves the padded input-position segment followed by the marker. The input position is at most $|x|+1$, so its bit representation fits in the prescribed width (`length_bits_pos_le`); the padding therefore has length exactly $w_P(|x|)$ (`length_padBits`). Taking that many bits selects precisely the padded segment.

**Key facts.** `Complexity.Codec.length_chunksWord`, `Complexity.Codec.length_bits_pos_le`, `Complexity.Codec.length_padBits`.
