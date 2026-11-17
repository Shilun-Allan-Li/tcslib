<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCountTape_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing at the Suffix Head

**Claim.** For bit lists $u$ and $v$ and a bit $b$, updating the tape holding $u$ followed by $v$ at cell $|u|$ with $b$ gives the tape holding $u$ followed by $b$ and then the tail of $v$.

**Proof.** Compare the two tape functions at an arbitrary cell $z$. If $z=|u|$, the tape-reading fact says that the old symbol there is the head of $v$; the update replaces it by $b$, which is exactly the symbol at that position in $u$ followed by $b$ and the tail of $v$ (`clCountTape_read`). If $z\ne |u|$, the update leaves the old value unchanged. For negative $z$, both tape readings are empty. For nonnegative $z$, split according to whether $z$ lies before the end of $u$. Before that boundary both lists read from $u$. After it, the old list reads from $v$ starting at the corresponding offset, while the new list reads from $b$ followed by the tail of $v$; since $z$ is not the boundary cell, these readings agree. Thus the two tape functions agree at every cell.
