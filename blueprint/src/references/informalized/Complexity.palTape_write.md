<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/Examples.lean :: Complexity.palTape_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending the Copied Prefix by One Bit

**Claim.** Writing $x_t$ at cell $t$ on the tape containing the first $t$ bits of $x$ gives the tape containing the first $t+1$ bits.

**Proof.** Compare the two tapes at each integer cell $z$. At $z=t$, the update writes $x_t$, which is exactly the value of the tape defined for the first $t+1$ bits at that cell. If $z\ne t$, the update leaves the old tape unchanged. For such a cell, the conditions $0\le z<t$ and $0\le z<t+1$ are equivalent: the only additional integer position admitted by the latter range is $t$. Thus the old and new tape values agree at every other cell as well.
