<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRedBuffer_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Literal Buffer

**Claim.** The buffer tape for the empty word with cut position $0$ is blank at every integer offset except $-1$, where it contains the bit $0$.

**Proof.** Compare the two tapes at an arbitrary integer offset $z$. If $z=-1$, the buffer definition gives the false marker, exactly as the update of the everywhere-blank tape does at its updated position. If $z\ne -1$, the update leaves the blank tape unchanged. The buffer definition is also blank there: for negative $z$ other than $-1$ its first condition fails, while for nonnegative $z$ the empty word has no entry at that offset. Thus the tapes agree at every offset.
