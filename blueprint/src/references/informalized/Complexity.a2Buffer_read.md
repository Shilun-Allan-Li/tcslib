<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2Buffer_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Buffer Read at a Suffix Boundary

**Claim.** For any Boolean words $\mathrm{pre}$ and $\mathrm{bs}$, reading the buffer tape for their concatenation at cell $|\mathrm{pre}|$ returns the first bit of $\mathrm{bs}$, or blank when $\mathrm{bs}$ is empty.

**Proof.** At the nonnegative position $|\mathrm{pre}|$, the buffer tape agrees with list lookup (`Turing.FinTM.bufferTape_nat`). Looking up this index in the concatenation skips exactly the prefix, so it is the lookup at index zero in $\mathrm{bs}$. That lookup is its head, and is blank precisely when the suffix is empty.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
