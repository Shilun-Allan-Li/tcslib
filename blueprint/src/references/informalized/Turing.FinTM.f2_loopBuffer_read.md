<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopBuffer_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the First Buffer Symbol

**Claim.** For Boolean words $\mathrm{pre}$ and $\mathrm{bs}$, the buffer storing their concatenation, read at position $|\mathrm{pre}|$, contains the first symbol of $\mathrm{bs}$ if one exists.

**Proof.** At a natural-number position, reading the buffer is the same as reading the list at that index (`bufferTape_nat`). In the concatenation $\mathrm{pre}\,\mathrm{bs}$, the index $|\mathrm{pre}|$ is the first index belonging to the second word. The list-index formula for appending therefore reduces this read to index zero of $\mathrm{bs}$. If $\mathrm{bs}$ is empty the result is none; if it is nonempty, the result is its head, as claimed.

**Key facts.** `Turing.FinTM.bufferTape_nat`.
