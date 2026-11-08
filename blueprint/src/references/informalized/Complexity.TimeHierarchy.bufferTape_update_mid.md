<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockLoop.lean :: Complexity.TimeHierarchy.bufferTape_update_mid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Middle-Symbol Tape Update

**Claim.** Updating the tape for $l++[a]++m$ at position $|l|$ to contain $b$ gives the tape for $l++[b]++m$.

**Proof.** Compare the two tape functions at an arbitrary integer position $z$. If $z=|l|$, both tapes are read at the middle position, and the update replaces $a$ by $b$. If $z\ne |l|$ and $z$ is nonnegative, then $z$ is a natural list index different from $|l|$. For indices before $|l|$, both concatenations return the same entry from $l$. For indices after $|l|$, both return the same entry from $m$, since the middle symbol occupies the same single position in each list. If $z$ is negative, both tape functions return none. Thus the functions agree at every integer position.
