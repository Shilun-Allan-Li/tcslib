<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCmp_forward_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Forward Scan Step

**Claim.** When $j$ is strictly below the maximum length of four Boolean words, one comparator step from the scanning configuration after $j$ columns advances the scanning control and all four work-tape heads to position $j+1$, leaving the input-head position and tape contents unchanged.

**Proof.** Because $j$ is strictly below the maximum word length, it is not the case that all four words have ended at position $j$; this follows from the equivalence between all four reads being blank and the maximum length being at most the position (`Complexity.clCmp_blank`). The comparator therefore takes its nonblank scanning branch. Its state update is precisely the next orbit state, and it moves each work-tape head one position forward without writing to the tapes. The symbols supplied to this transition are exactly the respective words' symbols at position $j$ (`Complexity.clCmp_read`). The input head does not move, so its position is unchanged (`Turing.moveInputPos_zero`).

**Key facts.** `Complexity.clCmp_blank`, `Complexity.clCmp_read`, `Turing.moveInputPos_zero`.
