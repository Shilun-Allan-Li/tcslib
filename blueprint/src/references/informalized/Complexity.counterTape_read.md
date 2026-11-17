<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.counterTape_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading After a Binary Prefix

**Claim.** For finite binary words $p$ and $b$, the tape formed by placing their concatenation on the nonnegative cells has, at position $|p|$, the first bit of $b$, or a blank if $b$ is empty.

**Proof.** At the nonnegative position $|p|$, the tape reads the list entry of $p++b$ at index $|p|$. The list concatenation indexing rule identifies this entry with the entry of $b$ at index $|p|-|p|=0$. If $b$ is empty, that lookup is absent; if it is nonempty, it is its first bit. The position is nonnegative, so the tape's negative-position blank case does not apply.
