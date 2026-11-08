<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRedCounter_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Tape Left Boundary

**Claim.** For every $n$, the unary counter tape of length $n$ is blank at offset $-1$.

**Proof.** The counter tape is the finite buffer associated with a replicated word. A buffer tape is blank at every negative offset; in particular, it is blank at $-1$ (the buffer left-boundary fact, `Turing.FinTM.bufferTape_left`).

**Key facts.** `Turing.FinTM.bufferTape_left`.
