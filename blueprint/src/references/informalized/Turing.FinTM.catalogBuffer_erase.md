<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogBuffer_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the final buffer cell

**Claim.** For every Boolean word $w$ and bit $b$, changing the buffer tape for $w$ followed by $b$ to blank at cell $|w|$ yields the buffer tape for $w$.

**Proof.** Appending $b$ extends the buffer tape for $w$ by updating cell $|w|$ to contain $b$ (`bufferTape_append`). Updating that same cell to blank cancels the previous update, by idempotence of function update with the same index. Equivalently, pointwise, at the index $|w|$ the resulting value is blank, and at every other index the update leaves the original buffer value unchanged. Hence the resulting tape is exactly the buffer tape for $w$.

**Key facts.** `Turing.FinTM.bufferTape_append`.
