<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.writeBlock_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a Written Block

**Claim.** If $j<|\beta|$, then after writing $\beta$ starting at position $i$, the bit at position $i+j$ is $\beta_j$, interpreted through the default-false list lookup.

**Proof.** At $v=i+j$, the write condition holds: $i\le i+j$, and $j<|\beta|$ gives $i+j<i+|\beta|$. The rule therefore reads the block at offset $(i+j)-i=j$, yielding $\beta.getD\,j\,\mathrm{false}$.
