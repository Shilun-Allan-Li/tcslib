<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputLength.lean :: Turing.inputLengthCfg_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Length Tape Overlay

**Claim.** Overlaying a word on a tape with overlay length zero and no head displacement changes only the state and input-head position as specified.

**Proof.** Compare the configuration fields. The state and input-head position are the chosen values, the work-head position is unchanged, and the output remains that of $d$. For any tape cell, the overlay condition requires the cell to be at least the work-head position and strictly less than that same position, since the overlay length is zero. No cell satisfies both inequalities, so the tape contents are everywhere those of $d$. Hence the resulting configuration is exactly $d$ with only the stated state and input-head position changed.
