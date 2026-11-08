<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clWipe_backward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Erasing Pass

**Claim.** For any target word $w$, the reset machine run from its erasing control, with stream $v$ at head position $s$ and target $w$ at head position $|w|-1$, takes $|w|+1$ steps to reach the completed control with the stream unchanged and the target blank at head position zero.

**Proof.** Use induction on the word by removing its final symbol. If the word is empty, one step takes the machine from the erasing control to the completed control; the input head stays fixed, and both tapes and heads have the asserted values. Now write a nonempty word as $u$ followed by a final bit $b$. At the target head position $|u|$, the buffer tape contains $b$ (`Turing.FinTM.bufferTape_nat`). The reset transition erases that last cell, moves the target head back to $|u|-1$, and leaves the stream and its head unchanged. The erased target tape is then precisely the buffer representation of $u$, by the last-cell erasure identity (`Complexity.clErase_last`). This single step changes the remaining run length from $|w|+1$ to $|u|+1$; the induction hypothesis finishes the run. The run decomposition into one step followed by the remaining steps is the successor law for runs (`Turing.MultiTapeTM.runFrom_succ_eq_step`), and the zero-time run law handles the base case (`Turing.MultiTapeTM.runFrom_zero`). Throughout, the input head is unchanged because a zero move leaves it fixed (`Turing.moveInputPos_zero`).

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Complexity.clErase_last`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
