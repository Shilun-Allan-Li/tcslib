<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopBuffer_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a Buffered Word

**Claim.** Changing cell $|p|$ in the buffer for $p$ followed by $u$ and then $b$ to the bit $v$ gives the buffer for $p$ followed by $v$ and then $b$.

**Proof.** Compare the two tape functions at an arbitrary integer position $z$. At $z=|p|$, the update writes $v$, which is exactly the value at that position in the new word. At any other position, the update leaves the old tape unchanged. Negative positions are blank on both tapes. For nonnegative positions before $|p|$, both concatenations return the same symbol from $p$; for positions after $|p|$, list indexing passes the single intervening bit and returns the same symbol from $b$ (or blank beyond the word). Thus the functions agree at every cell.
