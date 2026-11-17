<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCopy_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Copier Source Head

**Claim.** For every input word, valid input-head position, source word, record, and $j\le |w|$, running the copier for $j+1$ steps from its rewinding control with source head at $j-1$ reaches the completed control with source head zero, preserving the source word, record, input-head position, and output.

**Proof.** Induct on $j$. When $j=0$, the source head is at $-1$. The rewinding transition sees no source symbol there and moves the head to zero while entering the completed control; the work tapes, input-head position, and output are unchanged. For the successor case, the current source-head position is $j$, where $j<|w|$ by the bound hypothesis, so the source tape contains the list entry $w[j]$ (`Turing.FinTM.bufferTape_nat` and the list-index fact). The rewinding transition moves the head one cell left and keeps the rewinding control. The run decomposition (`Turing.MultiTapeTM.runFrom_succ_eq_step`) reduces the remaining run to the induction hypothesis, now starting at $j-1$ and taking $j+1$ steps. The induction concludes at head position zero with the other data preserved.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_nat`.
