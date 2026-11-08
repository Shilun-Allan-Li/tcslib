<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.dc_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decode Loop Execution

**Claim.** Under the stated suffix bounds, register bounds, initial pointer and accumulator values, and input-bit agreement, the codec program executes from the decode-test instruction to the next instruction for the identifier. At the endpoint the pointer is reset to the base, the accumulator contains the binary value of the word, and all other registers are unchanged; every earlier configuration is safe and bounded by $B$.

**Proof.** First, `dc_distinct` supplies the six pairwise inequalities among the pointer, base, accumulator, and temporary registers. The stride is positive for each decode identifier. The instructions of the codec at the relevant labels satisfy the hypotheses of the stride-based decoding loop: the test compares pointer and base; the prescribed number of decrements reaches the read instruction; the read queries the input bit at the pointer; and the copy, bump, clear, scale, take, increment, and add instructions have precisely the specified continuations. Applying `decodeStride_loop` with these registers and labels gives a bounded, guarded execution. Its oracle-answer hypothesis follows from the given input-bit agreement and the fact that the bit oracle on the pair encoding of $y$ and the binary representation of an index returns the corresponding bit of $y$ (`orc_bit`). The loop conclusion gives the pointer reset to its base, the accumulator equal to the value of $w$, the temporary register zero, and preservation of the other registers. Finally, `Reach.cast` adjusts the endpoint assignment to the stated nested register updates; the pairwise distinctness ensures these updates affect exactly the intended registers.

**Key facts.** `Complexity.Codec.dc_distinct`, `Complexity.Codec.decodeStride_loop`, `Complexity.Codec.orc_bit`, `Complexity.Codec.Reach.cast`.
