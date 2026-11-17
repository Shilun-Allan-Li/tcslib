<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecObserve_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Observation Equals Encoded Row Bit

**Claim.** If a configuration’s work-tape heads lie within radius $s$ and its tapes are blank outside that window, then its Boolean observation at each encoded bit position equals the corresponding bit of its encoded row.

**Proof.** It suffices to compare the two functions at each bit position. For input, input-head, state, and summary positions, the observation is defined directly by the corresponding component of the encoded row, so equality holds. At a work-tape position, the bit index selects one of three tests: whether the tape cell contains false, whether it contains true, or whether the head is at that cell. In the first two cases the observation and row use the same tape symbol. In the third case, the head lies within the radius-$s$ window by hypothesis; the position-code characterization (`codec_posCode_eq_iff`) says its encoded position equals the given cell index exactly when the actual head position equals that cell. Hence this test also agrees, proving the claim at every encoded position.

**Key facts.** `Complexity.codec_posCode_eq_iff`.
