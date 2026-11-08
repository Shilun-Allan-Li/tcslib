<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_overwrite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Overwrite the Next Buffer Cell

**Claim.** Updating the buffer tape for the concatenated word $\mathrm{pre}++\mathrm{old}$ at cell $|\mathrm{pre}|$ with $b$ gives the buffer tape for $\mathrm{pre}++b::\mathrm{old.drop\ 1}$.

**Proof.** Compare the two tape functions at an arbitrary integer cell $z$. If $z=|\mathrm{pre}|$, the update writes $b$, which is exactly the symbol at that position in the new concatenated word. Otherwise the update leaves the old tape value unchanged. For negative $z$, both buffer tapes are blank. For nonnegative $z$, its natural-number index differs from $|\mathrm{pre}|$. Indices before the end of $\mathrm{pre}$ see the same prefix in both words. At indices after the prefix, write the index as $|\mathrm{pre}|+1+m$; both words then read the same $m$th symbol of $\mathrm{old.drop\ 1}$, including the case where that list is empty. Hence the tape functions agree everywhere.
