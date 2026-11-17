<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_position_digits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Digits Track Input-Head Movement

**Claim.** The specified fixed-width digit update exists and equals the encoding of the input-head position after a left, stationary, or right move with boundary clamping.

**Proof.** Write $W=\mathrm{width}(|x|)$. The position bound `record_pos_lt` ensures that every valid position, and every increment needed below, fits in $W$ bits. For a stationary move, the head position and its digit word are unchanged.

For a left move, `moveInputPos_neg_val` identifies the new position as the old one minus one. At the left boundary the rule explicitly leaves the word unchanged. Otherwise, write the old position as $(n+1)$; the fixed-width digit theorem `recordStep_digits_succ` says that decrementing the digits of $n+1$ produces those of $n$, which is exactly the new position.

For a right move, `recordStep_right_clamp` identifies the rule's no-increment condition with being at the right boundary: the scanned symbol is absent there, and the head is not at the left boundary. At that boundary, `moveInputPos_rightBoundary` shows that clamping leaves the position fixed, so the digits stay unchanged. Away from it, `moveInputPos_pos_of_ne_right` says the new position is one greater than the old position. The increment half of `recordStep_digits_succ` then gives exactly its fixed-width encoding.

**Key facts.** `Turing.FinTM.moveInputPos_neg_val`, `Turing.record_pos_lt`, `Turing.recordStep_digits_succ`, `Turing.recordStep_right_clamp`, `Turing.moveInputPos_rightBoundary`, `Turing.moveInputPos_pos_of_ne_right`.
