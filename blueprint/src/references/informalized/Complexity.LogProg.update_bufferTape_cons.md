<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean :: Complexity.LogProg.update_bufferTape_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a Tape at a Word Position

**Claim.** Overwriting the tape storing $\mathrm{pre}++[b]++w$ at cell $|\mathrm{pre}|$ with $b'$ produces exactly the tape storing $\mathrm{pre}++[b']++w$.

**Proof.** Compare the two tape functions at an arbitrary integer cell $z$. If $z=|\mathrm{pre}|$, the update assigns $b'$ there, which is precisely the symbol at that position in the modified word. Otherwise the update leaves the old tape value unchanged. For a negative position both tape values are blank. For a nonnegative position, write its natural index as $z$. Since it is not $|\mathrm{pre}|$, it lies either in the prefix, where both words agree, or strictly after the overwritten position, where both words again have the same suffix entry. Thus the tape values agree at every cell, so the tape functions are equal.
