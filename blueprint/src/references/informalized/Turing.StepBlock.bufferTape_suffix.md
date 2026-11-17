<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.bufferTape_suffix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Buffer Tape Under a Nonnegative Shift

**Claim.** For a nonnegative integer $z$, the buffer tape storing a prefix followed by a word, read at position $|b|+z$, has the same content as the buffer tape storing just the word at position $z$.

**Proof.** Because $z\geq 0$, write it as its natural-number value. The integer position $|b|+z$ is then the natural position $|b|+z$, so the buffer-tape value is the list lookup at that index (`Turing.FinTM.bufferTape_nat`). A lookup in the concatenation at an index at least the prefix length reduces to the lookup in the suffix, with the prefix length subtracted. Here that suffix index is exactly $z$, giving the buffer-tape value of the word at $z$.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
