<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCountTape_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading at the Prefix Boundary

**Claim.** For bit lists $u$ and $v$, reading the tape holding their concatenation at cell $|u|$ returns the first bit of $v$, if it exists, and blank otherwise.

**Proof.** The boundary index $|u|$ is nonnegative, so the tape read is the list entry of $u ++ v$ at that index. The list-append indexing rule identifies this entry with the entry of $v$ at index $|u|-|u|=0$. The zeroth optional entry of a list is its head, including the empty-list case, so the read equals $v.head?$.
