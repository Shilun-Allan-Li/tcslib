<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogBuffer_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the Appended Bit

**Claim.** For every Boolean word $w$ and bit $b$, erasing the cell at position $|w|$ from the buffer tape containing $w$ followed by $b$ yields the buffer tape containing $w$.

**Proof.** By the buffer append formula (`bufferTape_append`), the tape containing $w$ followed by $b$ is obtained from the tape containing $w$ by updating the cell at position $|w|$ to `some b`. Updating that same cell to `none` afterward leaves every other cell unchanged and replaces the value at position $|w|$ by `none`. Pointwise, at that position the result agrees with the tape for $w$, which has no cell there; at every other position the appended-bit update had no effect, so the values still agree with the tape for $w$. Thus the two tapes are equal.

**Key facts.** `Turing.FinTM.bufferTape_append`.
