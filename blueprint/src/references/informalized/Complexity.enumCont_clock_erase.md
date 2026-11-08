<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_clock_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the Newest Clock Mark

**Claim.** Changing cell $n$ of the buffer tape containing $n+1$ consecutive true marks to blank yields the buffer tape containing $n$ consecutive true marks.

**Proof.** Write the list of $n+1$ marks as the list of $n$ marks followed by one final true mark. The buffer tape of a word followed by one symbol is obtained from the buffer tape of the word by updating the cell at the word's length to that symbol (`Turing.FinTM.bufferTape_append`). Here that length is $n$, so the longer tape is the shorter tape updated at cell $n$ to true. The shorter tape is blank at cell $n$, since its list has only positions $0$ through $n-1$. Replacing that cell's true mark by blank therefore restores the shorter buffer tape.

**Key facts.** `Turing.FinTM.bufferTape_append`.
