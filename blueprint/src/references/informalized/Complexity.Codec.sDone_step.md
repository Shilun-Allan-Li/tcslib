<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Step.lean :: Complexity.Codec.sDone_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Step Scan

**Claim.** The scan's acceptance flag is true exactly when $A'$ encodes the configuration obtained by applying $a$ to $C$ across the window of width $2s+1$, and that resulting configuration remains within distance $s$ of the origin on every work tape.

**Proof.** First, the blocks decoded from the encoding of the original configuration are exactly the sequence of its cells, by `blocksD_chunksWord`. Thus the scan compares the correct old cell at each position with the corresponding block of $A'$. The scan's acceptance flag is true precisely when each successive local update is correct, by the scan invariant `slide_ok_iff`: at each position, the proposed cell must equal the local rule applied to the current cell and its two neighbors, with empty cells supplied at the ends of the window.

The local characterization `slide_step_iff` identifies these local-rule equations with the cells of the configuration obtained by applying $a$, and its window hypothesis ensures that cells outside the window contribute only blanks and that the resulting configuration satisfies the required window condition. Hence, once the local equations hold, the proposed word is exactly the encoding of the updated configuration. More explicitly, equality of all decoded cells gives equality of the encoded chunks; `encChunk_of_decChunk` converts each successful decoding back to its encoded block, and `eq_flatten_blocks` reconstructs the full word from its equal-length blocks. Conversely, if $A'$ is that encoding and the updated configuration remains in the window, each block is the corresponding updated cell by `block_chunksWord`, so every local equation holds and the scan accepts. These two implications establish the equivalence.

**Key facts.** `Complexity.Codec.blocksD_chunksWord`, `Complexity.Codec.slide_ok_iff`, `Complexity.Codec.slide_step_iff`, `Complexity.Codec.encChunk_of_decChunk`, `Complexity.Codec.eq_flatten_blocks`, `Complexity.Codec.block_chunksWord`.
