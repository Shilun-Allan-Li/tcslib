<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_finish_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finalizer Erasure Phase

**Claim.** Starting the finalizer in state $4$ with the capture word $w$ and its head at $|w|-1$, after $|w|+1$ steps it reaches state $5$, leaves the argument tape unchanged, blanks the capture tape, places both work heads at the origin, and preserves the output.

**Proof.** Induct on $w$ by removing its last letter. For the empty word, the capture head is at $-1$, where the buffer is blank. The state-$4$ transition moves to state $5$ and sets the heads to the origin without altering either tape or the output; the zero-run and successor-run identities reduce the claim to this single step (`bufferTape_nil`, `runFrom_zero`, `runFrom_succ_eq_step`). For the inductive step, write $w=v b$. The symbol at cell $|v|$ is $b$ (`bufferTape_nat`), so the state-$4$ transition erases that cell, moves the capture head left, and leaves the argument tape and output fixed. Erasing the last cell of the buffer for $v b$ gives the buffer for $v$ (`emCall_erase_last`). The new head position is $|v|-1$, which is the inductive starting position, while the number of remaining steps is $|v|+1$. Applying the induction hypothesis clears the rest of the capture tape and reaches state $5$. Throughout, the input-head movement is zero, so its position is unchanged (`moveInputPos_zero`).

**Key facts.** `Turing.FinTM.bufferTape_nil`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.emCall_erase_last`, `Turing.moveInputPos_zero`.
