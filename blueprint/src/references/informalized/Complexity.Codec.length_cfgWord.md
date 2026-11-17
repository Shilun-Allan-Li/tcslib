<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.length_cfgWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration encoding length

**Claim.** The encoded configuration word has length $W(2s+1)+w_P(|x|)+1$.

**Proof.** The configuration word consists of the concatenated cell encodings, a padded binary encoding of the input-head position, and one final bit. By the fixed-width concatenation formula, the cell portion has length $W(2s+1)$ (`length_chunksWord`). The input-head position is a value strictly below $|x|+2$, by its membership in the corresponding finite type, and hence is at most $|x|+1$. Its binary representation therefore has length at most $w_P(|x|)$ (`length_bits_pos_le`); the padding lemma then says the padded portion has exactly that length (`length_padBits`). Adding the final single bit yields the asserted formula.

**Key facts.** `Complexity.Codec.length_bits_pos_le`, `Complexity.Codec.length_chunksWord`, `Complexity.Codec.length_padBits`.
