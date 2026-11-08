<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2Buffer_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Buffer Write at a Suffix Boundary

**Claim.** Overwriting cell $|\mathrm{pre}|$ of the buffer tape for $\mathrm{pre}\,\mathrm{old}\,\mathrm{bs}$ with $\mathrm{new}$ gives the buffer tape for $\mathrm{pre}\,\mathrm{new}\,\mathrm{bs}$.

**Proof.** Compare the two tape functions at an arbitrary integer cell. At the boundary cell $|\mathrm{pre}|$, the update replaces the old symbol by the new one, exactly as in the second concatenated word. At negative cells both tapes are blank. At any nonnegative cell strictly before the boundary, both words return the same symbol from the prefix. At a cell beyond the boundary, list lookup skips the prefix and the first suffix bit; replacing that bit changes only the boundary cell, so both tapes agree there as well. Hence the updated functions coincide at every cell.
