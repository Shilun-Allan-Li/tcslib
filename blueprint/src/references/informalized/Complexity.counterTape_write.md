<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.counterTape_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing at a Prefix Boundary

**Claim.** Overwriting position $|p|$ of the tape for the concatenation of $p$ and $b$ with $eta$ yields the tape for $p$ followed by $eta$ and then the tail of $b$.

**Proof.** Compare the two tapes at an arbitrary integer position $z$. At $z=|p|$, the tape reads the head bit of $b$ before the overwrite, and the overwrite sets that cell to $eta$; the tape-reading fact identifies the resulting value with the head of the new suffix ($\texttt{counterTape_read}$). At every other position, the update leaves the old tape unchanged. If $z<0$, both tapes read as empty. For nonnegative $z$, if $z<|p|$, both concatenations read the same cell in the prefix. Otherwise $z>|p|$, and removing the first suffix bit shifts the index by one, so the unchanged old cell agrees with the corresponding cell in the new word. Thus the tapes agree at every position.

**Key facts.** `Complexity.counterTape_read`.
