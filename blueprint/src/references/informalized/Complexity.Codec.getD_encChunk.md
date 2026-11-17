<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.getD_encChunk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded cell bit retrieval

**Claim.** For every position below the encoding width, retrieving that position from the encoded cell, with false as the out-of-range default, returns the corresponding chunk bit.

**Proof.** The encoding is the list obtained by evaluating the chunk-bit rule at every position in the finite range from $0$ to $W(N)-1$. Since $t<W(N)$, position $t$ is in that range, so list lookup returns exactly the value of the rule at $t$.
