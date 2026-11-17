<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMatch_commit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Committing a comparison flag

**Claim.** From the comparison-finished control holding verdict $b$, one step returns the matcher to the clock-test control, advances its clock to $j+1$, and appends $b$ to the flags while leaving the other displayed data unchanged.

**Proof.** In the comparison-finished state, the matcher transition moves to the clock-test control, makes no changes to the input head, and leaves the row, targets, stream, and cursor tapes untouched. It moves the clock head one position to the right and writes the bit $b$ at the current flag-tape head. Since that head is at the old flag length, this changes the flag tape from the buffer for `flags` to the buffer for `flags ++ [b]` and leaves its head at the new length. The buffer update is exactly the fact that appending one symbol writes that symbol at the previous length (`Turing.FinTM.bufferTape_append`). The input-head position is unchanged because a zero move preserves it (`Turing.moveInputPos_zero`). The configuration fields therefore match the claimed next configuration.

**Key facts.** `Turing.FinTM.bufferTape_append`, `Turing.moveInputPos_zero`.
