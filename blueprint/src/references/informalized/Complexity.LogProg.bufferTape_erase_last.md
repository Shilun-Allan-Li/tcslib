<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.bufferTape_erase_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the Final Tape Cell

**Claim.** Erasing the cell at position $|\mathit{pre}|$ from the tape storing $\mathit{pre}$ followed by $b$ yields the tape storing $\mathit{pre}$.

**Proof.** Compare the two tape functions at an arbitrary integer position $z$. If $z=|\mathit{pre}|$, the update makes the cell blank, and the tape for $\mathit{pre}$ is also blank there because its list has length $|\mathit{pre}|$. If $z$ differs from this position, the update leaves the cell unchanged. For nonnegative $z$, when its natural-number position is below $|\mathit{pre}|$, the list lookup in $\mathit{pre}++[b]$ agrees with the lookup in $\mathit{pre}$. When it is not below that length, both lookups are absent. For negative $z$, both tape functions are blank by definition. Thus the functions agree at every position.
