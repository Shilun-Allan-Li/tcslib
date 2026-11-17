<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean :: Complexity.LogProg.vpos_tmove -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Virtual Head Movement

**Claim.** For a valid tape position in an in-range segment, moving the tape head in either direction gives the same virtual position as moving the corresponding position in the bounded virtual input, provided the starting virtual position is in range.

**Proof.** First express the bounded-input move by its value formula (`moveInputPos_val`): a zero move preserves the position, a positive move advances by one but is capped at the right boundary, and a negative move subtracts one with the natural-number boundary convention. The segment-offset facts locate each segment within the virtual word: `off_add_rlen_le` bounds a segment’s end, `off_succ` gives the offset of the next segment, and `vpos_right_last` identifies the final segment’s right boundary with the end of the virtual word. The same offset recurrence also gives the relation to the preceding segment when one exists. The rendered lengths of plain and doubled segments are their word length and twice their word length, respectively (`rlen_false` and `rlen_true`).

Now fix the current segment and write it as a word together with its plain-or-doubled flag. Split on the movement direction and on whether the current tape position is the left boundary, a cell, or the right boundary. A zero move leaves both positions unchanged. For a positive move from the left boundary, the result is either the first cell or, for an empty segment, the right boundary. From a cell, the move advances within a doubled cell when its first half is current; otherwise it advances to the next cell or to the right boundary. From the right boundary, it enters the next segment’s left boundary when there is one, and otherwise stays at the final right boundary. The offset and length relations above show that these are exactly the increment-and-cap cases in the bounded virtual input.

For a negative move, the left boundary either stays put at the first segment or moves to the preceding segment’s right boundary. A cell moves to the other half of its doubled cell when appropriate; otherwise it moves to the previous cell or the left boundary. From the right boundary it moves to the last cell when the segment is nonempty, or to its left boundary when empty. In each case, the validity of the cell position and the offset relations identify the resulting virtual position with the decremented bounded-input position. The assumed range bound supplies the required bounded input position throughout.

**Key facts.** `Complexity.LogProg.moveInputPos_val`, `Complexity.LogProg.off_add_rlen_le`, `Complexity.LogProg.off_succ`, `Complexity.LogProg.vpos_right_last`, `Complexity.LogProg.rlen_false`, `Complexity.LogProg.rlen_true`.
