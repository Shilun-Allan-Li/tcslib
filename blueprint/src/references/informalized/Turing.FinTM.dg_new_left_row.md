<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_new_left_row -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# New left row after an action

**Claim.** Under the stated lower bound on all head positions and blankness at coordinate $a-1$, the row at $a-1$ after applying the action has no symbols, has cleared preceding-block flags, and marks tape $i$ exactly when its old head is at $a$ and the action moves that head left.

**Proof.** Compare the two rows entry by entry for each tape $i$. Since its old head position is at least $a$, it is not at $a-1$. The old cell at $a-1$ is blank by hypothesis. Applying the action therefore leaves that cell blank: if the action writes there, its head must have been at $a-1$, which is impossible; if it does not write, blankness is preserved. For the head flag, the new head is at $a-1$ exactly when the old head was at $a$ and the movement was left, as follows by checking the three possible movements. The preceding-block flag is cleared because the row is formed with that flag set to false. Thus each tape entry agrees with the prescribed left row, and the rows are equal.
