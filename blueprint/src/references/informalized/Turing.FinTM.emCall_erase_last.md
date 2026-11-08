<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_erase_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the Last Buffered Cell

**Claim.** Changing cell $|w|$ of the buffer tape storing $w$ followed by $b$ to blank gives exactly the buffer tape storing $w$.

**Proof.** The buffer tape for $w$ followed by $b$ is the buffer tape for $w$ updated at cell $|w|$ with $b$ (\texttt{bufferTape\_append}). Updating that same cell to blank cancels the appended-symbol update, since the later update overwrites the earlier one. Equivalently, at cell $|w|$ the result is blank, as is the tape for $w$; at every other cell both updates leave the value from the tape for $w$ unchanged. The buffer lookup at nonnegative integer positions is the corresponding list lookup (\texttt{bufferTape\_nat}), which justifies these cellwise comparisons.

**Key facts.** `Turing.FinTM.bufferTape_append`, `Turing.FinTM.bufferTape_nat`.
