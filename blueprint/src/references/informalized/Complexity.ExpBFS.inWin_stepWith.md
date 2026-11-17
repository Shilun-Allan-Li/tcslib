<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.inWin_stepWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Window Growth

**Claim.** If a configuration lies in the window of radius $s$, then after one transition with either choice bit it lies in the window of radius $s+1$.

**Proof.** If the configuration is already halted, a step leaves it unchanged, and enlarging the window preserves the window property by monotonicity (`Complexity.ExpBFS.inWin_mono`). Otherwise, fix a work tape. Its head moves by at most one cell, since the displacement between a configuration and its image under an action has absolute value at most one (`Turing.workTapePos_apply_le`). Thus its new distance from the origin is at most $s+1$. For blankness outside the enlarged window, such a cell $z$ is outside the old window as well. If the transition does not write on this tape, its contents there are unchanged and hence blank. If it writes, it changes only the cell at the old head position; that position lies within radius $s$, so it is not $z$. Therefore that cell remains blank in either case.

**Key facts.** `Complexity.ExpBFS.inWin_mono`, `Turing.workTapePos_apply_le`.
