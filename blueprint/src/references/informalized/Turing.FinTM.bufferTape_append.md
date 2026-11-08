<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.bufferTape_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending to a buffer tape

**Claim.** Appending $b$ to the word stored by a buffer tape is the same as updating cell $|w|$ to contain $b$.

**Proof.** Compare the two tapes at an arbitrary integer cell $z$. If $z=|w|$, the appended word has symbol $b$ at that cell, and the update also assigns $b$ there. If $z\ne |w|$ and $z$ is nonnegative, the update leaves the old tape value unchanged. The appended word agrees with $w$ at indices below $|w|$, while at indices above $|w|$ both list lookups are absent. If $z$ is negative, both tape values are absent by the definition of a buffer tape, and the update does not affect that cell. Thus the tapes agree at every cell.
