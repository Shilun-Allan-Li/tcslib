<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecRowBits_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of row bit encoding

**Claim.** For any finite Turing machine, input length, and window size, the map sending a codec row to its Boolean values on all codec-bit coordinates is injective.

**Proof.** Suppose two rows have the same Boolean value at every codec-bit coordinate. Their input functions agree pointwise by inspecting each input coordinate. At the state coordinate named by the first row's state, equality of encoded bits forces the second row to have that same state; likewise, the input-head coordinate named by the first row forces the heads to agree. For each work tape and cell, the two symbol coordinates record whether its optional symbol is false or true. Equality of both flags therefore makes the optional symbols equal, by the fact that these two flags distinguish all optional Boolean symbols (`Complexity.codec_symbol_ext`). The head-position coordinate at the first row's head location similarly forces the second row's head to agree. Finally, the two summary coordinates distinguish the three possible summaries, so equality of their bits makes the summaries equal. All fields of the rows consequently agree, and the rows are equal.

**Key facts.** `Complexity.codec_symbol_ext`.
