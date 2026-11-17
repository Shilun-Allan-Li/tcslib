<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codec_step_blank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank cells remain blank after a step

**Claim.** If every work-tape head of a configuration is within distance $s$ of the origin and all cells outside that interval are blank, then after one machine step all cells outside the interval are still blank.

**Proof.** Fix a tape and a position $z$ with $|z|>s$. If the configuration is already in the halting state, the machine leaves it unchanged, so the cell remains blank by the assumed blankness outside the interval. Otherwise, the machine applies its transition action. The head on the chosen tape lies within distance $s$, whereas $z$ lies outside, so the head is not at $z$. If the action makes no write on this tape, its contents are unchanged and hence blank at $z$. If it does write, the action updates the tape only at the head position; since that position is not $z$, the cell at $z$ remains unchanged and blank.
