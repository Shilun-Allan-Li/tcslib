<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopBuffer_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Buffer Frontier

**Claim.** For Boolean words $p$ and $b$, the buffer for their concatenation, read at cell $|p|$, contains the first bit of $b$ when $b$ is nonempty and is blank when $b$ is empty.

**Proof.** The read position is a natural number, so the buffer agrees there with list indexing (`bufferTape_nat`). In the concatenation $p++b$, the index $|p|$ is exactly the first position belonging to $b$. The list-indexing rule for an appended list therefore identifies the read with $b$'s head option, which is the first bit when $b$ is nonempty and none when it is empty.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
